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

module MAlonzo.Code.Once.Optimize where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Optimize._≟Functor_
d__'8799'Functor__8 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Functor__8 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v3
               -> coe
                    du_'8799'Functor'45'K'45'aux_314
                    (coe d__'8799'Type__120 (coe v2) (coe v3))
             MAlonzo.Code.Once.Type.C_Id_112
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__114 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__116 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Id_112
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_112
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_112
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__114 v4 v5
               -> coe
                    du_'8799'Functor'45''8853''45'aux_328
                    (coe d__'8799'Functor__8 (coe v2) (coe v4))
                    (coe d__'8799'Functor__8 (coe v3) (coe v5))
             MAlonzo.Code.Once.Type.C__'8855'__116 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_112
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__114 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__116 v4 v5
               -> coe
                    du_'8799'Functor'45''8855''45'aux_350
                    (coe d__'8799'Functor__8 (coe v2) (coe v4))
                    (coe d__'8799'Functor__8 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Type-*-aux
d_'8799'Type'45''42''45'aux_18 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Type'45''42''45'aux_18 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'Type'45''42''45'aux_18 v4 v5
du_'8799'Type'45''42''45'aux_18 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45''42''45'aux_18 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Type-+-aux
d_'8799'Type'45''43''45'aux_40 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Type'45''43''45'aux_40 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'Type'45''43''45'aux_40 v4 v5
du_'8799'Type'45''43''45'aux_40 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45''43''45'aux_40 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Type-⇒-aux
d_'8799'Type'45''8658''45'aux_66 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Type'45''8658''45'aux_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8799'Type'45''8658''45'aux_66 v6 v7 v8
du_'8799'Type'45''8658''45'aux_66 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45''8658''45'aux_66 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (case coe v2 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                          -> if coe v7
                                               then coe
                                                      seq (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v7)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                            erased))
                                               else coe
                                                      seq (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v7)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v6)
                                     (case coe v2 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                          -> coe
                                               seq (coe v7)
                                               (coe
                                                  seq (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v5)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> coe
                              seq (coe v5)
                              (coe
                                 seq (coe v6)
                                 (case coe v2 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                      -> coe
                                           seq (coe v7)
                                           (coe
                                              seq (coe v8)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                 (coe v3)
                                                 (coe
                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Type-μ-aux
d_'8799'Type'45'μ'45'aux_100 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Type'45'μ'45'aux_100 ~v0 ~v1 v2
  = du_'8799'Type'45'μ'45'aux_100 v2
du_'8799'Type'45'μ'45'aux_100 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45'μ'45'aux_100 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Type-ν-aux
d_'8799'Type'45'ν'45'aux_110 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Type'45'ν'45'aux_110 ~v0 ~v1 v2
  = du_'8799'Type'45'ν'45'aux_110 v2
du_'8799'Type'45'ν'45'aux_110 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45'ν'45'aux_110 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟Type_
d__'8799'Type__120 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Type__120 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Void_120
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v4 v5
               -> coe
                    du_'8799'Type'45''42''45'aux_18
                    (coe d__'8799'Type__120 (coe v2) (coe v4))
                    (coe d__'8799'Type__120 (coe v3) (coe v5))
             MAlonzo.Code.Once.Type.C__'43'__124 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v4 v5
               -> coe
                    du_'8799'Type'45''43''45'aux_40
                    (coe d__'8799'Type__120 (coe v2) (coe v4))
                    (coe d__'8799'Type__120 (coe v3) (coe v5))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v5 v6 v7
               -> coe
                    du_'8799'Type'45''8658''45'aux_66
                    (coe d__'8799'Type__120 (coe v2) (coe v5))
                    (coe MAlonzo.Code.Once.Type.d__'8799'k__96 (coe v3) (coe v6))
                    (coe d__'8799'Type__120 (coe v4) (coe v7))
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
               -> coe
                    du_'8799'Type'45'μ'45'aux_100
                    (coe d__'8799'Functor__8 (coe v2) (coe v3))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
               -> coe
                    du_'8799'Type'45'ν'45'aux_110
                    (coe d__'8799'Functor__8 (coe v2) (coe v3))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_132
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Float_134
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Str_136
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Functor-K-aux
d_'8799'Functor'45'K'45'aux_314 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Functor'45'K'45'aux_314 ~v0 ~v1 v2
  = du_'8799'Functor'45'K'45'aux_314 v2
du_'8799'Functor'45'K'45'aux_314 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Functor'45'K'45'aux_314 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Functor-⊕-aux
d_'8799'Functor'45''8853''45'aux_328 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Functor'45''8853''45'aux_328 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'Functor'45''8853''45'aux_328 v4 v5
du_'8799'Functor'45''8853''45'aux_328 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Functor'45''8853''45'aux_328 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Functor-⊗-aux
d_'8799'Functor'45''8855''45'aux_350 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Functor'45''8855''45'aux_350 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'Functor'45''8855''45'aux_350 v4 v5
du_'8799'Functor'45''8855''45'aux_350 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Functor'45''8855''45'aux_350 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.IRHead
d_IRHead_408 = ()
data T_IRHead_408
  = C_h'45'id_410 | C_h'45''8728'_412 |
    C_h'45''10216''44''10217'_414 | C_h'45'fst_416 | C_h'45'snd_418 |
    C_h'45'inl_420 | C_h'45'inr_422 | C_h'45'case_424 |
    C_h'45'terminal_426 | C_h'45'initial_428 | C_h'45'curry_430 |
    C_h'45'apply_432 | C_h'45'arr_434 | C_h'45'In_436 |
    C_h'45'out'45'μ_438 | C_h'45'Cata_440 | C_h'45'Para_442 |
    C_h'45'Out_444 | C_h'45'in'45'ν_446 | C_h'45'Ana_448 |
    C_h'45'Hylo_450 | C_h'45'Fuse_452 | C_h'45'free'45'heap_454 |
    C_h'45'SigOp_456 | C_h'45'const_458
-- Once.Optimize.headTag
d_headTag_460 :: T_IRHead_408 -> Integer
d_headTag_460 v0
  = case coe v0 of
      C_h'45'id_410 -> coe (0 :: Integer)
      C_h'45''8728'_412 -> coe (1 :: Integer)
      C_h'45''10216''44''10217'_414 -> coe (2 :: Integer)
      C_h'45'fst_416 -> coe (3 :: Integer)
      C_h'45'snd_418 -> coe (4 :: Integer)
      C_h'45'inl_420 -> coe (5 :: Integer)
      C_h'45'inr_422 -> coe (6 :: Integer)
      C_h'45'case_424 -> coe (7 :: Integer)
      C_h'45'terminal_426 -> coe (8 :: Integer)
      C_h'45'initial_428 -> coe (9 :: Integer)
      C_h'45'curry_430 -> coe (10 :: Integer)
      C_h'45'apply_432 -> coe (11 :: Integer)
      C_h'45'arr_434 -> coe (12 :: Integer)
      C_h'45'In_436 -> coe (14 :: Integer)
      C_h'45'out'45'μ_438 -> coe (15 :: Integer)
      C_h'45'Cata_440 -> coe (16 :: Integer)
      C_h'45'Para_442 -> coe (17 :: Integer)
      C_h'45'Out_444 -> coe (18 :: Integer)
      C_h'45'in'45'ν_446 -> coe (19 :: Integer)
      C_h'45'Ana_448 -> coe (20 :: Integer)
      C_h'45'Hylo_450 -> coe (21 :: Integer)
      C_h'45'Fuse_452 -> coe (22 :: Integer)
      C_h'45'free'45'heap_454 -> coe (23 :: Integer)
      C_h'45'SigOp_456 -> coe (24 :: Integer)
      C_h'45'const_458 -> coe (25 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.headTag-inj
d_headTag'45'inj_466 ::
  T_IRHead_408 ->
  T_IRHead_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_headTag'45'inj_466 = erased
-- Once.Optimize._≟IRHead_
d__'8799'IRHead__472 ::
  T_IRHead_408 ->
  T_IRHead_408 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRHead__472 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe d_headTag_460 (coe v0)))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    eqInt (coe d_headTag_460 (coe v0))
                    (coe d_headTag_460 (coe v1)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.ir-head
d_ir'45'head_500 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_IRHead_408
d_ir'45'head_500 ~v0 ~v1 v2 = du_ir'45'head_500 v2
du_ir'45'head_500 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_IRHead_408
du_ir'45'head_500 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe C_h'45'id_410
      MAlonzo.Code.Once.IR.C__'8728'__30 v2 v4 v5
        -> coe C_h'45''8728'_412
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v4 v5
        -> coe C_h'45''10216''44''10217'_414
      MAlonzo.Code.Once.IR.C_fst_44 -> coe C_h'45'fst_416
      MAlonzo.Code.Once.IR.C_snd_50 -> coe C_h'45'snd_418
      MAlonzo.Code.Once.IR.C_inl_56 -> coe C_h'45'inl_420
      MAlonzo.Code.Once.IR.C_inr_62 -> coe C_h'45'inr_422
      MAlonzo.Code.Once.IR.C_case_70 v4 v5 -> coe C_h'45'case_424
      MAlonzo.Code.Once.IR.C_terminal_74 -> coe C_h'45'terminal_426
      MAlonzo.Code.Once.IR.C_initial_78 -> coe C_h'45'initial_428
      MAlonzo.Code.Once.IR.C_curry_86 v4 -> coe C_h'45'curry_430
      MAlonzo.Code.Once.IR.C_apply_92 -> coe C_h'45'apply_432
      MAlonzo.Code.Once.IR.C_In_96 v2 -> coe C_h'45'In_436
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v2 -> coe C_h'45'out'45'μ_438
      MAlonzo.Code.Once.IR.C_Cata_108 v2 v5 -> coe C_h'45'Cata_440
      MAlonzo.Code.Once.IR.C_Para_114 v2 v4 -> coe C_h'45'Para_442
      MAlonzo.Code.Once.IR.C_Out_118 v2 -> coe C_h'45'Out_444
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v2 -> coe C_h'45'in'45'ν_446
      MAlonzo.Code.Once.IR.C_Ana_128 v2 v4 -> coe C_h'45'Ana_448
      MAlonzo.Code.Once.IR.C_Hylo_136 v1 v3 v4 v6 v7
        -> coe C_h'45'Hylo_450
      MAlonzo.Code.Once.IR.C_Fuse_144 v1 v3 v4 v6 v7
        -> coe C_h'45'Fuse_452
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v1
        -> coe C_h'45'free'45'heap_454
      MAlonzo.Code.Once.IR.C_const_150 v2 v3 -> coe C_h'45'const_458
      MAlonzo.Code.Once.IR.C_SigOp_156 v1 v2 v3 -> coe C_h'45'SigOp_456
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.subst₂-IR
d_subst'8322''45'IR_510 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_subst'8322''45'IR_510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_subst'8322''45'IR_510 v6
du_subst'8322''45'IR_510 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_subst'8322''45'IR_510 v0 = coe v0
-- Once.Optimize.uipK
d_uipK_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uipK_526 = erased
-- Once.Optimize.sigop-dom
d_sigop'45'dom_532 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_sigop'45'dom_532 ~v0 ~v1 v2 = du_sigop'45'dom_532 v2
du_sigop'45'dom_532 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
du_sigop'45'dom_532 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IR.C_SigOp_156 v2 v3 v4
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
         _ -> coe v1)
-- Once.Optimize.sigop-cod
d_sigop'45'cod_542 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_sigop'45'cod_542 ~v0 ~v1 v2 = du_sigop'45'cod_542 v2
du_sigop'45'cod_542 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
du_sigop'45'cod_542 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IR.C_SigOp_156 v2 v3 v4
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
         _ -> coe v1)
-- Once.Optimize.sigop-dom-subst
d_sigop'45'dom'45'subst_562 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'dom'45'subst_562 = erased
-- Once.Optimize.sigop-cod-subst
d_sigop'45'cod'45'subst_580 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'cod'45'subst_580 = erased
-- Once.Optimize.ir-head-subst₂
d_ir'45'head'45'subst'8322'_598 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'head'45'subst'8322'_598 = erased
-- Once.Optimize.head-mismatch-abs
d_head'45'mismatch'45'abs_616 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_head'45'mismatch'45'abs_616 = erased
-- Once.Optimize.cross-no
d_cross'45'no_646 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cross'45'no_646 = erased
-- Once.Optimize.≟IRH
d_'8799'IRH_674 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH_674 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_'8799'IRH_674 v0 v1 v2 v3 v4 v5
du_'8799'IRH_674 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH_674 v0 v1 v2 v3 v4 v5
  = coe
      du_'8799'IRH'45'aux_710 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
      (coe
         d__'8799'IRHead__472 (coe du_ir'45'head_500 (coe v4))
         (coe du_ir'45'head_500 (coe v5)))
-- Once.Optimize.≟IRH-diag
d_'8799'IRH'45'diag_692 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'diag_692 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_'8799'IRH'45'diag_692 v0 v1 v2 v3 v4 v5
du_'8799'IRH'45'diag_692 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'diag_692 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C__'8728'__30 v12 v14 v15
               -> coe
                    du_'8799'IRH'45''8728''45'aux_1104 (coe v0) (coe v7) (coe v1)
                    (coe v9) (coe v10) (coe v14) (coe v15)
                    (coe MAlonzo.Code.Once.IRTy.d__'8799'IRTy__208 (coe v7) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v16 v17
                      -> coe
                           du_'8799'IRH'45''10216''44''10217''45'aux_1140
                           (coe
                              du_'8799'IRH_674 (coe v0) (coe v11) (coe v0) (coe v11) (coe v9)
                              (coe v16))
                           (coe
                              du_'8799'IRH_674 (coe v0) (coe v12) (coe v0) (coe v12) (coe v10)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_inl_56
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_inr_62
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_case_70 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_case_70 v16 v17
                      -> coe
                           du_'8799'IRH'45'case'45'aux_1200
                           (coe
                              du_'8799'IRH_674 (coe v11) (coe v1) (coe v11) (coe v1) (coe v9)
                              (coe v16))
                           (coe
                              du_'8799'IRH_674 (coe v12) (coe v1) (coe v12) (coe v1) (coe v10)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_curry_86 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_curry_86 v15
                      -> coe
                           du_'8799'IRH'45'curry'45'aux_1256
                           (coe
                              du_'8799'IRH_674
                              (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                              (coe v11)
                              (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                              (coe v11) (coe v9) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_In_96 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    seq (coe v5)
                    (case coe v3 of
                       MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
                         -> let v10
                                  = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226 (coe v8) (coe v9) in
                            coe
                              (case coe v10 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                   -> if coe v11
                                        then coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                     erased))
                                        else coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    seq (coe v5)
                    (case coe v2 of
                       MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
                         -> let v10
                                  = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226 (coe v8) (coe v9) in
                            coe
                              (case coe v10 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                   -> if coe v11
                                        then coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                     erased))
                                        else coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_108 v7 v10
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> case coe v5 of
                           MAlonzo.Code.Once.IR.C_Cata_108 v15 v18
                             -> case coe v2 of
                                  MAlonzo.Code.Once.IRTy.C__'42'__20 v19 v20
                                    -> case coe v20 of
                                         MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v21
                                           -> let v22
                                                    = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226
                                                        (coe v13) (coe v21) in
                                              coe
                                                (case coe v22 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                     -> if coe v23
                                                          then coe
                                                                 seq (coe v24)
                                                                 (let v25
                                                                        = coe
                                                                            du_'8799'IRH'45'aux_710
                                                                            (coe
                                                                               MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                               (coe v11)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                                  (coe v13)
                                                                                  (coe v1)))
                                                                            (coe v1)
                                                                            (coe
                                                                               MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                               (coe v11)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                                  (coe v13)
                                                                                  (coe v1)))
                                                                            (coe v1) (coe v10)
                                                                            (coe v18)
                                                                            (let v25
                                                                                   = coe
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                       erased
                                                                                       (\ v25 ->
                                                                                          coe
                                                                                            MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                                            (coe
                                                                                               d_headTag_460
                                                                                               (coe
                                                                                                  du_ir'45'head_500
                                                                                                  (coe
                                                                                                     v10))))
                                                                                       (coe
                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                          (coe
                                                                                             eqInt
                                                                                             (coe
                                                                                                d_headTag_460
                                                                                                (coe
                                                                                                   du_ir'45'head_500
                                                                                                   (coe
                                                                                                      v10)))
                                                                                             (coe
                                                                                                d_headTag_460
                                                                                                (coe
                                                                                                   du_ir'45'head_500
                                                                                                   (coe
                                                                                                      v18))))
                                                                                          (coe
                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                                             (coe
                                                                                                eqInt
                                                                                                (coe
                                                                                                   d_headTag_460
                                                                                                   (coe
                                                                                                      du_ir'45'head_500
                                                                                                      (coe
                                                                                                         v10)))
                                                                                                (coe
                                                                                                   d_headTag_460
                                                                                                   (coe
                                                                                                      du_ir'45'head_500
                                                                                                      (coe
                                                                                                         v18)))))) in
                                                                             coe
                                                                               (case coe v25 of
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                    -> if coe v26
                                                                                         then coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v27)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                   (coe
                                                                                                      v26)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                      erased))
                                                                                         else coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v27)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                   (coe
                                                                                                      v26)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                                  coe
                                                                    (case coe v25 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                         -> if coe v26
                                                                              then coe
                                                                                     seq (coe v27)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v26)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                           erased))
                                                                              else coe
                                                                                     seq (coe v27)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v26)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          else coe
                                                                 seq (coe v24)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                    (coe v23)
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v7 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_Para_114 v12 v14
                      -> case coe v2 of
                           MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v15
                             -> let v16
                                      = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226
                                          (coe v10) (coe v15) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                       -> if coe v17
                                            then coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = coe
                                                              du_'8799'IRH'45'aux_710
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                 (coe v10)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                    (coe v0) (coe v1)))
                                                              (coe v1)
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                 (coe v10)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                    (coe v0) (coe v1)))
                                                              (coe v1) (coe v9) (coe v14)
                                                              (let v19
                                                                     = coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                         erased
                                                                         (\ v19 ->
                                                                            coe
                                                                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                              (coe
                                                                                 d_headTag_460
                                                                                 (coe
                                                                                    du_ir'45'head_500
                                                                                    (coe v9))))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe
                                                                               eqInt
                                                                               (coe
                                                                                  d_headTag_460
                                                                                  (coe
                                                                                     du_ir'45'head_500
                                                                                     (coe v9)))
                                                                               (coe
                                                                                  d_headTag_460
                                                                                  (coe
                                                                                     du_ir'45'head_500
                                                                                     (coe v14))))
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                               (coe
                                                                                  eqInt
                                                                                  (coe
                                                                                     d_headTag_460
                                                                                     (coe
                                                                                        du_ir'45'head_500
                                                                                        (coe v9)))
                                                                                  (coe
                                                                                     d_headTag_460
                                                                                     (coe
                                                                                        du_ir'45'head_500
                                                                                        (coe
                                                                                           v14)))))) in
                                                               coe
                                                                 (case coe v19 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                      -> if coe v20
                                                                           then coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                     (coe v20)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                        erased))
                                                                           else coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                     (coe v20)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                    coe
                                                      (case coe v19 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                           -> if coe v20
                                                                then coe
                                                                       seq (coe v21)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v20)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased))
                                                                else coe
                                                                       seq (coe v21)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v20)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            else coe
                                                   seq (coe v18)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v17)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_118 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    seq (coe v5)
                    (case coe v2 of
                       MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
                         -> let v10
                                  = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226 (coe v8) (coe v9) in
                            coe
                              (case coe v10 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                   -> if coe v11
                                        then coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                     erased))
                                        else coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    seq (coe v5)
                    (case coe v3 of
                       MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
                         -> let v10
                                  = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226 (coe v8) (coe v9) in
                            coe
                              (case coe v10 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                   -> if coe v11
                                        then coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                     erased))
                                        else coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_128 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_Ana_128 v12 v14
                      -> case coe v3 of
                           MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v15
                             -> let v16
                                      = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226
                                          (coe v10) (coe v15) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                       -> if coe v17
                                            then coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = coe
                                                              du_'8799'IRH'45'aux_710 (coe v0)
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                 (coe v10) (coe v0))
                                                              (coe v0)
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                 (coe v10) (coe v0))
                                                              (coe v9) (coe v14)
                                                              (let v19
                                                                     = coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                         erased
                                                                         (\ v19 ->
                                                                            coe
                                                                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                              (coe
                                                                                 d_headTag_460
                                                                                 (coe
                                                                                    du_ir'45'head_500
                                                                                    (coe v9))))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe
                                                                               eqInt
                                                                               (coe
                                                                                  d_headTag_460
                                                                                  (coe
                                                                                     du_ir'45'head_500
                                                                                     (coe v9)))
                                                                               (coe
                                                                                  d_headTag_460
                                                                                  (coe
                                                                                     du_ir'45'head_500
                                                                                     (coe v14))))
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                               (coe
                                                                                  eqInt
                                                                                  (coe
                                                                                     d_headTag_460
                                                                                     (coe
                                                                                        du_ir'45'head_500
                                                                                        (coe v9)))
                                                                                  (coe
                                                                                     d_headTag_460
                                                                                     (coe
                                                                                        du_ir'45'head_500
                                                                                        (coe
                                                                                           v14)))))) in
                                                               coe
                                                                 (case coe v19 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                      -> if coe v20
                                                                           then coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                     (coe v20)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                        erased))
                                                                           else coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                     (coe v20)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                    coe
                                                      (case coe v19 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                           -> if coe v20
                                                                then coe
                                                                       seq (coe v21)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v20)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased))
                                                                else coe
                                                                       seq (coe v21)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v20)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            else coe
                                                   seq (coe v18)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v17)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Hylo_136 v6 v8 v9 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_Hylo_136 v14 v16 v17 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v21
                             -> let v22
                                      = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226
                                          (coe v13) (coe v21) in
                                coe
                                  (case coe v22 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                       -> if coe v23
                                            then coe
                                                   seq (coe v24)
                                                   (let v25
                                                          = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226
                                                              (coe v6) (coe v14) in
                                                    coe
                                                      (case coe v25 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                           -> if coe v26
                                                                then coe
                                                                       seq (coe v27)
                                                                       (coe
                                                                          du_'8799'IRH'45'Hylo'45'inner_1292
                                                                          (coe
                                                                             du_'8799'IRH_674
                                                                             (coe
                                                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                                (coe v6) (coe v1))
                                                                             (coe v1)
                                                                             (coe
                                                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                                (coe v6) (coe v1))
                                                                             (coe v1) (coe v11)
                                                                             (coe v19))
                                                                          (coe
                                                                             d__'8799'NatTr__768
                                                                             (coe v13) (coe v6)
                                                                             (coe v12) (coe v20)))
                                                                else coe
                                                                       seq (coe v27)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v26)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            else coe
                                                   seq (coe v24)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v23)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Fuse_144 v6 v8 v9 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_Fuse_144 v14 v16 v17 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v21
                             -> let v22
                                      = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226
                                          (coe v13) (coe v21) in
                                coe
                                  (case coe v22 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                       -> if coe v23
                                            then coe
                                                   seq (coe v24)
                                                   (let v25
                                                          = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__226
                                                              (coe v6) (coe v14) in
                                                    coe
                                                      (case coe v25 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                           -> if coe v26
                                                                then coe
                                                                       seq (coe v27)
                                                                       (coe
                                                                          du_'8799'IRH'45'Fuse'45'inner_1352
                                                                          (coe
                                                                             du_'8799'IRH_674
                                                                             (coe
                                                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                                (coe v6) (coe v1))
                                                                             (coe v1)
                                                                             (coe
                                                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                                                                (coe v6) (coe v1))
                                                                             (coe v1) (coe v11)
                                                                             (coe v19))
                                                                          (coe
                                                                             d__'8799'NatTr__768
                                                                             (coe v13) (coe v6)
                                                                             (coe v12) (coe v20)))
                                                                else coe
                                                                       seq (coe v27)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v26)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            else coe
                                                   seq (coe v24)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v23)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v6
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C_free'45'heap_146 v7
               -> let v8
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v8 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                 (coe MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12 (coe v6)))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                               (coe
                                  eqInt
                                  (coe MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12 (coe v6))
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12 (coe v7)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                  (coe
                                     eqInt
                                     (coe
                                        MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                        (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                        (coe v7))))) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then let v11
                                         = seq
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v9)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                   erased)) in
                                   coe
                                     (case coe v11 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> if coe v12
                                               then coe
                                                      seq (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                            erased))
                                               else coe
                                                      seq (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else (let v11
                                          = seq
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                    coe
                                      (case coe v11 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                           -> if coe v12
                                                then coe
                                                       seq (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                             erased))
                                                else coe
                                                       seq (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                         _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_150 v7 v8
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C_const_150 v10 v11
               -> coe
                    d_'8799'const'45'irrelevant_2578 v1 v7 v8 v10 v11 erased v7 v10 v8
                    v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_156 v6 v7 v8
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C_SigOp_156 v9 v10 v11
               -> let v12 = d__'8799'Type__120 (coe v6) (coe v9) in
                  coe
                    (let v13 = d__'8799'Type__120 (coe v7) (coe v10) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then coe
                                        seq (coe v15)
                                        (case coe v13 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                             -> if coe v16
                                                  then coe
                                                         seq (coe v17)
                                                         (let v18
                                                                = coe
                                                                    MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                                    (coe
                                                                       MAlonzo.Code.Data.String.Properties.d__'8799'__54)
                                                                    (coe
                                                                       MAlonzo.Code.Once.CanonicalName.d_parts_8
                                                                       (coe
                                                                          MAlonzo.Code.Once.SigOp.Info.d_name_174
                                                                          (coe v8)))
                                                                    (coe
                                                                       MAlonzo.Code.Once.CanonicalName.d_parts_8
                                                                       (coe
                                                                          MAlonzo.Code.Once.SigOp.Info.d_name_174
                                                                          (coe v11))) in
                                                          coe
                                                            (case coe v18 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                 -> if coe v19
                                                                      then let v21
                                                                                 = seq
                                                                                     (coe v20)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v19)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                           erased)) in
                                                                           coe
                                                                             (case coe v21 of
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                  -> if coe v22
                                                                                       then let v24
                                                                                                  = seq
                                                                                                      (coe
                                                                                                         v23)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                         (coe
                                                                                                            v22)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                            erased)) in
                                                                                            coe
                                                                                              (case coe
                                                                                                      v24 of
                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                   -> if coe
                                                                                                           v25
                                                                                                        then coe
                                                                                                               seq
                                                                                                               (coe
                                                                                                                  v26)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                  (coe
                                                                                                                     v25)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                     erased))
                                                                                                        else coe
                                                                                                               seq
                                                                                                               (coe
                                                                                                                  v26)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                  (coe
                                                                                                                     v25)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                       else (let v24
                                                                                                   = seq
                                                                                                       (coe
                                                                                                          v23)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                          (coe
                                                                                                             v22)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v24 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                    -> if coe
                                                                                                            v25
                                                                                                         then coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v26)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                   (coe
                                                                                                                      v25)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                      erased))
                                                                                                         else coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v26)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                   (coe
                                                                                                                      v25)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                      else (let v21
                                                                                  = seq
                                                                                      (coe v20)
                                                                                      (coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                         (coe v19)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                            coe
                                                                              (case coe v21 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                   -> if coe v22
                                                                                        then let v24
                                                                                                   = seq
                                                                                                       (coe
                                                                                                          v23)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                          (coe
                                                                                                             v22)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                             erased)) in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v24 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                    -> if coe
                                                                                                            v25
                                                                                                         then coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v26)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                   (coe
                                                                                                                      v25)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                      erased))
                                                                                                         else coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v26)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                   (coe
                                                                                                                      v25)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                        else (let v24
                                                                                                    = seq
                                                                                                        (coe
                                                                                                           v23)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                           (coe
                                                                                                              v22)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                                              coe
                                                                                                (case coe
                                                                                                        v24 of
                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                     -> if coe
                                                                                                             v25
                                                                                                          then coe
                                                                                                                 seq
                                                                                                                 (coe
                                                                                                                    v26)
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                    (coe
                                                                                                                       v25)
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                       erased))
                                                                                                          else coe
                                                                                                                 seq
                                                                                                                 (coe
                                                                                                                    v26)
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                    (coe
                                                                                                                       v25)
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                  else coe
                                                         seq (coe v17)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 else coe
                                        seq (coe v15)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v14)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-aux
d_'8799'IRH'45'aux_710 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'aux_710 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_'8799'IRH'45'aux_710 v0 v1 v2 v3 v4 v5 v6
du_'8799'IRH'45'aux_710 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'aux_710 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       du_'8799'IRH'45'diag_692 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5))
             else coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v7)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟IR_
d__'8799'IR__748 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IR__748 v0 v1 v2 v3
  = coe
      du_'8799'IRH_674 (coe v0) (coe v1) (coe v0) (coe v1) (coe v2)
      (coe v3)
-- Once.Optimize.nt-headTag
d_nt'45'headTag_758 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> Integer
d_nt'45'headTag_758 ~v0 ~v1 v2 = du_nt'45'headTag_758 v2
du_nt'45'headTag_758 :: MAlonzo.Code.Once.IR.T_NatTr_18 -> Integer
du_nt'45'headTag_758 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_ntId_158 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_ntK_164 v3 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_ntFst_172 v4 -> coe (2 :: Integer)
      MAlonzo.Code.Once.IR.C_ntSnd_180 v4 -> coe (3 :: Integer)
      MAlonzo.Code.Once.IR.C_ntCase_188 v4 v5 -> coe (4 :: Integer)
      MAlonzo.Code.Once.IR.C_ntInl_196 v4 -> coe (5 :: Integer)
      MAlonzo.Code.Once.IR.C_ntInr_204 v4 -> coe (6 :: Integer)
      MAlonzo.Code.Once.IR.C_ntPair_212 v4 v5 -> coe (7 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟NatTr_
d__'8799'NatTr__768 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'NatTr__768 v0 v1 v2 v3
  = coe
      d_'8799'NatTr'45'aux_778 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe du_nt'45'headTag_758 (coe v2))
         (coe du_nt'45'headTag_758 (coe v3)))
-- Once.Optimize.≟NatTr-aux
d_'8799'NatTr'45'aux_778 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'NatTr'45'aux_778 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       du_'8799'NatTr'45'diag_788 (coe v0) (coe v1) (coe v2) (coe v3))
             else coe
                    seq (coe v6)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v5)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟NatTr-diag
d_'8799'NatTr'45'diag_788 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'NatTr'45'diag_788 v0 v1 v2 v3 ~v4
  = du_'8799'NatTr'45'diag_788 v0 v1 v2 v3
du_'8799'NatTr'45'diag_788 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'NatTr'45'diag_788 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_158
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_ntK_164 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v7
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_K_8 v8
                      -> case coe v3 of
                           MAlonzo.Code.Once.IR.C_ntK_164 v11
                             -> let v12
                                      = coe
                                          du_'8799'IRH'45'aux_710 (coe v7) (coe v8) (coe v7)
                                          (coe v8) (coe v6) (coe v11)
                                          (let v12
                                                 = coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                     erased
                                                     (\ v12 ->
                                                        coe
                                                          MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                          (coe
                                                             d_headTag_460
                                                             (coe du_ir'45'head_500 (coe v6))))
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                        (coe
                                                           eqInt
                                                           (coe
                                                              d_headTag_460
                                                              (coe du_ir'45'head_500 (coe v6)))
                                                           (coe
                                                              d_headTag_460
                                                              (coe du_ir'45'head_500 (coe v11))))
                                                        (coe
                                                           MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                           (coe
                                                              eqInt
                                                              (coe
                                                                 d_headTag_460
                                                                 (coe du_ir'45'head_500 (coe v6)))
                                                              (coe
                                                                 d_headTag_460
                                                                 (coe
                                                                    du_ir'45'head_500
                                                                    (coe v11)))))) in
                                           coe
                                             (case coe v12 of
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                  -> if coe v13
                                                       then coe
                                                              seq (coe v14)
                                                              (coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v13)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                    erased))
                                                       else coe
                                                              seq (coe v14)
                                                              (coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v13)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                _ -> MAlonzo.RTE.mazUnreachableError)) in
                                coe
                                  (case coe v12 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                       -> if coe v13
                                            then coe
                                                   seq (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                         erased))
                                            else coe
                                                   seq (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_172 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_ntFst_172 v13
                      -> let v14
                               = d_'8799'NatTr'45'aux_778
                                   (coe v8) (coe v1) (coe v7) (coe v13)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_758 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_758 (coe v7))
                                            (coe du_nt'45'headTag_758 (coe v13)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_758 (coe v7))
                                               (coe du_nt'45'headTag_758 (coe v13)))))) in
                         coe
                           (case coe v14 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                -> if coe v15
                                     then coe
                                            seq (coe v16)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  erased))
                                     else coe
                                            seq (coe v16)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_180 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_ntSnd_180 v13
                      -> let v14
                               = d_'8799'NatTr'45'aux_778
                                   (coe v9) (coe v1) (coe v7) (coe v13)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_758 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_758 (coe v7))
                                            (coe du_nt'45'headTag_758 (coe v13)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_758 (coe v7))
                                               (coe du_nt'45'headTag_758 (coe v13)))))) in
                         coe
                           (case coe v14 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                -> if coe v15
                                     then coe
                                            seq (coe v16)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  erased))
                                     else coe
                                            seq (coe v16)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_188 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_ntCase_188 v14 v15
                      -> let v16
                               = d_'8799'NatTr'45'aux_778
                                   (coe v9) (coe v1) (coe v7) (coe v14)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v16 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_758 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_758 (coe v7))
                                            (coe du_nt'45'headTag_758 (coe v14)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_758 (coe v7))
                                               (coe du_nt'45'headTag_758 (coe v14)))))) in
                         coe
                           (let v17
                                  = d_'8799'NatTr'45'aux_778
                                      (coe v10) (coe v1) (coe v8) (coe v15)
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v17 ->
                                            coe
                                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                              (coe du_nt'45'headTag_758 (coe v8)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe
                                               eqInt (coe du_nt'45'headTag_758 (coe v8))
                                               (coe du_nt'45'headTag_758 (coe v15)))
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                               (coe
                                                  eqInt (coe du_nt'45'headTag_758 (coe v8))
                                                  (coe du_nt'45'headTag_758 (coe v15)))))) in
                            coe
                              (let v18
                                     = case coe v17 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                           -> coe
                                                seq (coe v18)
                                                (coe
                                                   seq (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                         _ -> MAlonzo.RTE.mazUnreachableError in
                               coe
                                 (case coe v16 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                      -> let v21
                                               = case coe v17 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                     -> case coe v21 of
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                            -> case coe v22 of
                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                   -> coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                        (coe v21)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                 _ -> coe v18
                                                          _ -> coe v18
                                                   _ -> MAlonzo.RTE.mazUnreachableError in
                                         coe
                                           (if coe v19
                                              then case coe v20 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                       -> case coe v17 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                              -> case coe v23 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v24 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v23)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                    erased)
                                                                          _ -> coe v21
                                                                   _ -> coe v21
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v21
                                              else (case coe v20 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                        -> coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v19)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                      _ -> coe v21))
                                    _ -> MAlonzo.RTE.mazUnreachableError)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_196 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_ntInl_196 v13
                      -> let v14
                               = d_'8799'NatTr'45'aux_778
                                   (coe v0) (coe v8) (coe v7) (coe v13)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_758 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_758 (coe v7))
                                            (coe du_nt'45'headTag_758 (coe v13)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_758 (coe v7))
                                               (coe du_nt'45'headTag_758 (coe v13)))))) in
                         coe
                           (case coe v14 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                -> if coe v15
                                     then coe
                                            seq (coe v16)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  erased))
                                     else coe
                                            seq (coe v16)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_204 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_ntInr_204 v13
                      -> let v14
                               = d_'8799'NatTr'45'aux_778
                                   (coe v0) (coe v9) (coe v7) (coe v13)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_758 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_758 (coe v7))
                                            (coe du_nt'45'headTag_758 (coe v13)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_758 (coe v7))
                                               (coe du_nt'45'headTag_758 (coe v13)))))) in
                         coe
                           (case coe v14 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                -> if coe v15
                                     then coe
                                            seq (coe v16)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  erased))
                                     else coe
                                            seq (coe v16)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_212 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_ntPair_212 v14 v15
                      -> let v16
                               = d_'8799'NatTr'45'aux_778
                                   (coe v0) (coe v9) (coe v7) (coe v14)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v16 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_758 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_758 (coe v7))
                                            (coe du_nt'45'headTag_758 (coe v14)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_758 (coe v7))
                                               (coe du_nt'45'headTag_758 (coe v14)))))) in
                         coe
                           (let v17
                                  = d_'8799'NatTr'45'aux_778
                                      (coe v0) (coe v10) (coe v8) (coe v15)
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v17 ->
                                            coe
                                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                              (coe du_nt'45'headTag_758 (coe v8)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe
                                               eqInt (coe du_nt'45'headTag_758 (coe v8))
                                               (coe du_nt'45'headTag_758 (coe v15)))
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                               (coe
                                                  eqInt (coe du_nt'45'headTag_758 (coe v8))
                                                  (coe du_nt'45'headTag_758 (coe v15)))))) in
                            coe
                              (let v18
                                     = case coe v17 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                           -> coe
                                                seq (coe v18)
                                                (coe
                                                   seq (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                         _ -> MAlonzo.RTE.mazUnreachableError in
                               coe
                                 (case coe v16 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                      -> let v21
                                               = case coe v17 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                     -> case coe v21 of
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                            -> case coe v22 of
                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                   -> coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                        (coe v21)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                 _ -> coe v18
                                                          _ -> coe v18
                                                   _ -> MAlonzo.RTE.mazUnreachableError in
                                         coe
                                           (if coe v19
                                              then case coe v20 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                       -> case coe v17 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                              -> case coe v23 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v24 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v23)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                    erased)
                                                                          _ -> coe v21
                                                                   _ -> coe v21
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v21
                                              else (case coe v20 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                        -> coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v19)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                      _ -> coe v21))
                                    _ -> MAlonzo.RTE.mazUnreachableError)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.μ-inj
d_μ'45'inj_1000 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_μ'45'inj_1000 = erased
-- Once.Optimize.*-injˡ
d_'42''45'inj'737'_1010 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'inj'737'_1010 = erased
-- Once.Optimize.*-injʳ
d_'42''45'inj'691'_1020 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'inj'691'_1020 = erased
-- Once.Optimize.ν-inj
d_ν'45'inj_1026 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ν'45'inj_1026 = erased
-- Once.Optimize.≟IRH-∘-inner
d_'8799'IRH'45''8728''45'inner_1042 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''8728''45'inner_1042 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                    v8
  = du_'8799'IRH'45''8728''45'inner_1042 v7 v8
du_'8799'IRH'45''8728''45'inner_1042 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''8728''45'inner_1042 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-∘-aux
d_'8799'IRH'45''8728''45'aux_1104 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''8728''45'aux_1104 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8799'IRH'45''8728''45'aux_1104 v0 v1 v3 v4 v5 v6 v7 v8
du_'8799'IRH'45''8728''45'aux_1104 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''8728''45'aux_1104 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       du_'8799'IRH'45''8728''45'inner_1042
                       (coe
                          du_'8799'IRH_674 (coe v1) (coe v2) (coe v1) (coe v2) (coe v3)
                          (coe v5))
                       (coe
                          du_'8799'IRH_674 (coe v0) (coe v1) (coe v0) (coe v1) (coe v4)
                          (coe v6)))
             else coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-⟨,⟩-aux
d_'8799'IRH'45''10216''44''10217''45'aux_1140 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''10216''44''10217''45'aux_1140 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 ~v6 v7 v8
  = du_'8799'IRH'45''10216''44''10217''45'aux_1140 v7 v8
du_'8799'IRH'45''10216''44''10217''45'aux_1140 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''10216''44''10217''45'aux_1140 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-case-aux
d_'8799'IRH'45'case'45'aux_1200 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'case'45'aux_1200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_'8799'IRH'45'case'45'aux_1200 v7 v8
du_'8799'IRH'45'case'45'aux_1200 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'case'45'aux_1200 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-curry-aux
d_'8799'IRH'45'curry'45'aux_1256 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'curry'45'aux_1256 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8799'IRH'45'curry'45'aux_1256 v5
du_'8799'IRH'45'curry'45'aux_1256 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'curry'45'aux_1256 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-Hylo-inner
d_'8799'IRH'45'Hylo'45'inner_1292 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'Hylo'45'inner_1292 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 v11 v12
  = du_'8799'IRH'45'Hylo'45'inner_1292 v11 v12
du_'8799'IRH'45'Hylo'45'inner_1292 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'Hylo'45'inner_1292 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-Fuse-inner
d_'8799'IRH'45'Fuse'45'inner_1352 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'Fuse'45'inner_1352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 v11 v12
  = du_'8799'IRH'45'Fuse'45'inner_1352 v11 v12
du_'8799'IRH'45'Fuse'45'inner_1352 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'Fuse'45'inner_1352 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._.≟const-irrelevant
d_'8799'const'45'irrelevant_2578
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Optimize._.\8799const-irrelevant"
-- Once.Optimize.dec-to-bool
d_dec'45'to'45'bool_2584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
d_dec'45'to'45'bool_2584 ~v0 ~v1 v2 = du_dec'45'to'45'bool_2584 v2
du_dec'45'to'45'bool_2584 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
du_dec'45'to'45'bool_2584 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe seq (coe v2) (coe v1)
             else coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-Void
d_is'45'Void_2586 :: MAlonzo.Code.Once.Type.T_Type_108 -> Bool
d_is'45'Void_2586 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C__'42'__122 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'43'__124 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isUnitType
d_isUnitType_2588 :: MAlonzo.Code.Once.Type.T_Type_108 -> Bool
d_isUnitType_2588 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'42'__122 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'43'__124 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isVoidType
d_isVoidType_2590 :: MAlonzo.Code.Once.Type.T_Type_108 -> Bool
d_isVoidType_2590 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C__'42'__122 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'43'__124 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-fst?
d_is'45'fst'63'_2596 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'fst'63'_2596 ~v0 ~v1 v2 = du_is'45'fst'63'_2596 v2
du_is'45'fst'63'_2596 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'fst'63'_2596 v0
  = coe
      du_dec'45'to'45'bool_2584
      (coe
         d__'8799'IRHead__472 (coe du_ir'45'head_500 (coe v0))
         (coe C_h'45'fst_416))
-- Once.Optimize.is-snd?
d_is'45'snd'63'_2604 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'snd'63'_2604 ~v0 ~v1 v2 = du_is'45'snd'63'_2604 v2
du_is'45'snd'63'_2604 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'snd'63'_2604 v0
  = coe
      du_dec'45'to'45'bool_2584
      (coe
         d__'8799'IRHead__472 (coe du_ir'45'head_500 (coe v0))
         (coe C_h'45'snd_418))
-- Once.Optimize.is-terminal?
d_is'45'terminal'63'_2612 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'terminal'63'_2612 ~v0 ~v1 v2
  = du_is'45'terminal'63'_2612 v2
du_is'45'terminal'63'_2612 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'terminal'63'_2612 v0
  = coe
      du_dec'45'to'45'bool_2584
      (coe
         d__'8799'IRHead__472 (coe du_ir'45'head_500 (coe v0))
         (coe C_h'45'terminal_426))
-- Once.Optimize.safe-pair-distrib
d_safe'45'pair'45'distrib_2624 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_safe'45'pair'45'distrib_2624 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_safe'45'pair'45'distrib_2624 v4 v5
du_safe'45'pair'45'distrib_2624 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_safe'45'pair'45'distrib_2624 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe du_is'45'fst'63'_2596 (coe v0))
         (coe du_is'45'snd'63'_2604 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe du_is'45'snd'63'_2604 (coe v0))
            (coe du_is'45'fst'63'_2596 (coe v1)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe du_is'45'terminal'63'_2612 (coe v0))
            (coe du_is'45'terminal'63'_2612 (coe v1))))
-- Once.Optimize.wants-coprod
d_wants'45'coprod_2634 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_wants'45'coprod_2634 ~v0 ~v1 v2 = du_wants'45'coprod_2634 v2
du_wants'45'coprod_2634 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_wants'45'coprod_2634 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         du_dec'45'to'45'bool_2584
         (coe
            d__'8799'IRHead__472 (coe du_ir'45'head_500 (coe v0))
            (coe C_h'45'case_424)))
      (coe
         du_dec'45'to'45'bool_2584
         (coe
            d__'8799'IRHead__472 (coe du_ir'45'head_500 (coe v0))
            (coe C_h'45'terminal_426)))
-- Once.Optimize.PairView
d_PairView_2644 a0 a1 a2 a3 = ()
data T_PairView_2644
  = C_is'45'pair_2656 | C_is'45'other'45'pair_2666
-- Once.Optimize.CoprodView
d_CoprodView_2674 a0 a1 a2 a3 = ()
data T_CoprodView_2674
  = C_is'45'inl_2680 | C_is'45'inr_2686 |
    C_is'45'other'45'coprod_2696
-- Once.Optimize.ComposeFirstView
d_ComposeFirstView_2702 a0 a1 a2 = ()
data T_ComposeFirstView_2702
  = C_cf'45'id_2706 | C_cf'45'terminal_2710 | C_cf'45'fst_2716 |
    C_cf'45'snd_2722 | C_cf'45'case_2734 | C_cf'45'other_2742
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_2748 a0 a1 a2 = ()
data T_ComposeSecondView_2748
  = C_cs'45'id_2752 | C_cs'45'initial_2756 | C_cs'45'other_2764
-- Once.Optimize.FstSndView
d_FstSndView_2770 a0 a1 a2 = ()
data T_FstSndView_2770
  = C_fsv'45'fst_2776 | C_fsv'45'snd_2782 | C_fsv'45'other_2790
-- Once.Optimize.InlInrView
d_InlInrView_2796 a0 a1 a2 = ()
data T_InlInrView_2796
  = C_iiv'45'inl_2802 | C_iiv'45'inr_2808 | C_iiv'45'other_2816
-- Once.Optimize.pairView-gen
d_pairView'45'gen_2830 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_2644
d_pairView'45'gen_2830 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_2830 v2
du_pairView'45'gen_2830 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_2644
du_pairView'45'gen_2830 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C__'8728'__30 v2 v4 v5
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v4 v5
        -> coe C_is'45'pair_2656
      MAlonzo.Code.Once.IR.C_fst_44 -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_snd_50 -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_inl_56 -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_inr_62 -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_case_70 v4 v5
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_initial_78 -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_curry_86 v4
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_apply_92 -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_In_96 v2 -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v2
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_Cata_108 v2 v5
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_Para_114 v2 v4
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_Out_118 v2 -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v2
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_Ana_128 v2 v4
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_Hylo_136 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_Fuse_144 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v1
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_const_150 v2 v3
        -> coe C_is'45'other'45'pair_2666
      MAlonzo.Code.Once.IR.C_SigOp_156 v1 v2 v3
        -> coe C_is'45'other'45'pair_2666
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.pairView
d_pairView_2944 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_2644
d_pairView_2944 ~v0 ~v1 ~v2 v3 = du_pairView_2944 v3
du_pairView_2944 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_2644
du_pairView_2944 v0 = coe du_pairView'45'gen_2830 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_2960 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CoprodView_2674
d_coprodView'45'gen_2960 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_2960 v2
du_coprodView'45'gen_2960 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_2674
du_coprodView'45'gen_2960 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C__'8728'__30 v2 v4 v5
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v4 v5
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_fst_44 -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_snd_50 -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_inl_56 -> coe C_is'45'inl_2680
      MAlonzo.Code.Once.IR.C_inr_62 -> coe C_is'45'inr_2686
      MAlonzo.Code.Once.IR.C_case_70 v4 v5
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_curry_86 v4
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_apply_92 -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_In_96 v2 -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v2
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_Cata_108 v2 v5
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_Para_114 v2 v4
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_Out_118 v2
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v2
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_Ana_128 v2 v4
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_Hylo_136 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_Fuse_144 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v1
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_const_150 v2 v3
        -> coe C_is'45'other'45'coprod_2696
      MAlonzo.Code.Once.IR.C_SigOp_156 v1 v2 v3
        -> coe C_is'45'other'45'coprod_2696
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.coprodView
d_coprodView_3072 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_2674
d_coprodView_3072 ~v0 ~v1 ~v2 v3 = du_coprodView_3072 v3
du_coprodView_3072 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_2674
du_coprodView_3072 v0 = coe du_coprodView'45'gen_2960 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_3082 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_2702
d_composeFirstView_3082 ~v0 ~v1 v2 = du_composeFirstView_3082 v2
du_composeFirstView_3082 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_2702
du_composeFirstView_3082 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe C_cf'45'id_2706
      MAlonzo.Code.Once.IR.C__'8728'__30 v2 v4 v5
        -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v4 v5
        -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_fst_44 -> coe C_cf'45'fst_2716
      MAlonzo.Code.Once.IR.C_snd_50 -> coe C_cf'45'snd_2722
      MAlonzo.Code.Once.IR.C_inl_56 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_inr_62 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_case_70 v4 v5 -> coe C_cf'45'case_2734
      MAlonzo.Code.Once.IR.C_terminal_74 -> coe C_cf'45'terminal_2710
      MAlonzo.Code.Once.IR.C_initial_78 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_curry_86 v4 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_apply_92 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_In_96 v2 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v2 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_Cata_108 v2 v5 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_Para_114 v2 v4 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_Out_118 v2 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v2 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_Ana_128 v2 v4 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_Hylo_136 v1 v3 v4 v6 v7
        -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_Fuse_144 v1 v3 v4 v6 v7
        -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v1
        -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_const_150 v2 v3 -> coe C_cf'45'other_2742
      MAlonzo.Code.Once.IR.C_SigOp_156 v1 v2 v3 -> coe C_cf'45'other_2742
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_3148 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_2748
d_composeSecondView_3148 ~v0 ~v1 v2 = du_composeSecondView_3148 v2
du_composeSecondView_3148 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_2748
du_composeSecondView_3148 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe C_cs'45'id_2752
      MAlonzo.Code.Once.IR.C__'8728'__30 v2 v4 v5
        -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v4 v5
        -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_fst_44 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_snd_50 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_inl_56 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_inr_62 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_case_70 v4 v5 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_terminal_74 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_initial_78 -> coe C_cs'45'initial_2756
      MAlonzo.Code.Once.IR.C_curry_86 v4 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_apply_92 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_In_96 v2 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v2 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_Cata_108 v2 v5 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_Para_114 v2 v4 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_Out_118 v2 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v2 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_Ana_128 v2 v4 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_Hylo_136 v1 v3 v4 v6 v7
        -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_Fuse_144 v1 v3 v4 v6 v7
        -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v1
        -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_const_150 v2 v3 -> coe C_cs'45'other_2764
      MAlonzo.Code.Once.IR.C_SigOp_156 v1 v2 v3 -> coe C_cs'45'other_2764
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_3214 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_2770
d_fstSndView_3214 ~v0 ~v1 v2 = du_fstSndView_3214 v2
du_fstSndView_3214 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_2770
du_fstSndView_3214 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C__'8728'__30 v2 v4 v5
        -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v4 v5
        -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_fst_44 -> coe C_fsv'45'fst_2776
      MAlonzo.Code.Once.IR.C_snd_50 -> coe C_fsv'45'snd_2782
      MAlonzo.Code.Once.IR.C_inl_56 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_inr_62 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_case_70 v4 v5 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_terminal_74 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_initial_78 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_curry_86 v4 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_apply_92 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_In_96 v2 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v2 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_Cata_108 v2 v5 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_Para_114 v2 v4 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_Out_118 v2 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v2 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_Ana_128 v2 v4 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_Hylo_136 v1 v3 v4 v6 v7
        -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_Fuse_144 v1 v3 v4 v6 v7
        -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v1
        -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_const_150 v2 v3 -> coe C_fsv'45'other_2790
      MAlonzo.Code.Once.IR.C_SigOp_156 v1 v2 v3
        -> coe C_fsv'45'other_2790
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_3280 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_2796
d_inlInrView_3280 ~v0 ~v1 v2 = du_inlInrView_3280 v2
du_inlInrView_3280 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_2796
du_inlInrView_3280 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C__'8728'__30 v2 v4 v5
        -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v4 v5
        -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_fst_44 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_snd_50 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_inl_56 -> coe C_iiv'45'inl_2802
      MAlonzo.Code.Once.IR.C_inr_62 -> coe C_iiv'45'inr_2808
      MAlonzo.Code.Once.IR.C_case_70 v4 v5 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_terminal_74 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_initial_78 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_curry_86 v4 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_apply_92 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_In_96 v2 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v2 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_Cata_108 v2 v5 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_Para_114 v2 v4 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_Out_118 v2 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v2 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_Ana_128 v2 v4 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_Hylo_136 v1 v3 v4 v6 v7
        -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_Fuse_144 v1 v3 v4 v6 v7
        -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v1
        -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_const_150 v2 v3 -> coe C_iiv'45'other_2816
      MAlonzo.Code.Once.IR.C_SigOp_156 v1 v2 v3
        -> coe C_iiv'45'other_2816
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?
d_has'45'effect'63'_3344 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_has'45'effect'63'_3344 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C__'8728'__30 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'effect'63'_3344 (coe v4) (coe v1) (coe v6))
             (coe d_has'45'effect'63'_3344 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_3344 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63'_3344 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_inl_56
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_inr_62
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_case_70 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_3344 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63'_3344 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_curry_86 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    d_has'45'effect'63'_3344
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_In_96 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_Cata_108 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           d_has'45'effect'63'_3344
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v1)))
                           (coe v1) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    d_has'45'effect'63'_3344
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v7)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
                    (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_118 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_Ana_128 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    d_has'45'effect'63'_3344 (coe v0)
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v7) (coe v0))
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Hylo_136 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe
                       d_has'45'effect'63'_3344
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (coe d_has'45'effect'63''45'nt_3350 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Fuse_144 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe
                       d_has'45'effect'63'_3344
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (coe d_has'45'effect'63''45'nt_3350 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_const_150 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_SigOp_156 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?-nt
d_has'45'effect'63''45'nt_3350 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> Bool
d_has'45'effect'63''45'nt_3350 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_158
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_ntK_164 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_K_8 v7
                      -> coe d_has'45'effect'63'_3344 (coe v6) (coe v7) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_172 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe d_has'45'effect'63''45'nt_3350 (coe v7) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_180 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe d_has'45'effect'63''45'nt_3350 (coe v8) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_188 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63''45'nt_3350 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63''45'nt_3350 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_196 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe d_has'45'effect'63''45'nt_3350 (coe v0) (coe v7) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_204 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe d_has'45'effect'63''45'nt_3350 (coe v0) (coe v8) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_212 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63''45'nt_3350 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63''45'nt_3350 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-fst
d_optimize'45'fst_3404 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'fst_3404 ~v0 v1 v2 v3
  = du_optimize'45'fst_3404 v1 v2 v3
du_optimize'45'fst_3404 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'fst_3404 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_2830 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_2656
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v12 v13 -> coe v12
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_2666
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__30
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_fst_44) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-snd
d_optimize'45'snd_3426 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'snd_3426 ~v0 v1 v2 v3
  = du_optimize'45'snd_3426 v1 v2 v3
du_optimize'45'snd_3426 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'snd_3426 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_2830 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_2656
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v12 v13 -> coe v13
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_2666
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__30
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_snd_50) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_3450 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'post'45'case_3450 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_3450 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_3450 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'post'45'case_3450 v0 v1 v2 v3 v4
  = let v5 = coe du_coprodView'45'gen_2960 (coe v4) in
    coe
      (case coe v5 of
         C_is'45'inl_2680 -> coe v2
         C_is'45'inr_2686 -> coe v3
         C_is'45'other'45'coprod_2696
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__30
                (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_case_70 v2 v3) v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_3520 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose'45'second_3520 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_3520 v1 v3 v4
du_optimize'45'compose'45'second_3520 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'compose'45'second_3520 v0 v1 v2
  = let v3 = coe du_composeSecondView_3148 (coe v2) in
    coe
      (case coe v3 of
         C_cs'45'id_2752 -> coe v1
         C_cs'45'initial_2756 -> coe MAlonzo.Code.Once.IR.C_initial_78
         C_cs'45'other_2764
           -> coe MAlonzo.Code.Once.IR.C__'8728'__30 v0 v1 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose
d_optimize'45'compose_3550 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose_3550 v0 v1 v2 v3 v4
  = let v5 = d_has'45'effect'63'_3344 (coe v0) (coe v1) (coe v4) in
    coe
      (if coe v5
         then coe MAlonzo.Code.Once.IR.C__'8728'__30 v1 v3 v4
         else (let v6 = coe du_composeFirstView_3082 (coe v3) in
               coe
                 (case coe v6 of
                    C_cf'45'id_2706 -> coe v4
                    C_cf'45'terminal_2710 -> coe MAlonzo.Code.Once.IR.C_terminal_74
                    C_cf'45'fst_2716
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'fst_3404 (coe v2) (coe v10) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'snd_2722
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'snd_3426 (coe v9) (coe v2) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'case_2734
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Once.IR.C_case_70 v17 v18
                                    -> coe
                                         du_optimize'45'post'45'case_3450 (coe v12) (coe v13)
                                         (coe v17) (coe v18) (coe v4)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'other_2742
                      -> coe
                           du_optimize'45'compose'45'second_3520 (coe v1) (coe v3) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Optimize.optimize-pair-aux
d_optimize'45'pair'45'aux_3612 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_2770 ->
  T_FstSndView_2770 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair'45'aux_3612 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'pair'45'aux_3612 v3 v4 v5 v6
du_optimize'45'pair'45'aux_3612 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_2770 ->
  T_FstSndView_2770 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair'45'aux_3612 v0 v1 v2 v3
  = case coe v2 of
      C_fsv'45'fst_2776
        -> case coe v3 of
             C_fsv'45'fst_2776
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                    (coe MAlonzo.Code.Once.IR.C_fst_44)
                    (coe MAlonzo.Code.Once.IR.C_fst_44)
             C_fsv'45'snd_2782 -> coe MAlonzo.Code.Once.IR.C_id_22
             C_fsv'45'other_2790
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                    (coe MAlonzo.Code.Once.IR.C_fst_44) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'snd_2782
        -> case coe v3 of
             C_fsv'45'fst_2776
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                    (coe MAlonzo.Code.Once.IR.C_snd_50)
                    (coe MAlonzo.Code.Once.IR.C_fst_44)
             C_fsv'45'snd_2782
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                    (coe MAlonzo.Code.Once.IR.C_snd_50)
                    (coe MAlonzo.Code.Once.IR.C_snd_50)
             C_fsv'45'other_2790
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                    (coe MAlonzo.Code.Once.IR.C_snd_50) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'other_2790
        -> case coe v3 of
             C_fsv'45'fst_2776
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v0
                    (coe MAlonzo.Code.Once.IR.C_fst_44)
             C_fsv'45'snd_2782
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v0
                    (coe MAlonzo.Code.Once.IR.C_snd_50)
             C_fsv'45'other_2790
               -> coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_3656 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair_3656 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'pair_3656 v3 v4
du_optimize'45'pair_3656 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair_3656 v0 v1
  = coe
      du_optimize'45'pair'45'aux_3612 (coe v0) (coe v1)
      (coe du_fstSndView_3214 (coe v0)) (coe du_fstSndView_3214 (coe v1))
-- Once.Optimize.optimize-case-aux
d_optimize'45'case'45'aux_3672 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_2796 ->
  T_InlInrView_2796 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case'45'aux_3672 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'case'45'aux_3672 v3 v4 v5 v6
du_optimize'45'case'45'aux_3672 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_2796 ->
  T_InlInrView_2796 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case'45'aux_3672 v0 v1 v2 v3
  = case coe v2 of
      C_iiv'45'inl_2802
        -> case coe v3 of
             C_iiv'45'inl_2802
               -> coe
                    MAlonzo.Code.Once.IR.C_case_70 (coe MAlonzo.Code.Once.IR.C_inl_56)
                    (coe MAlonzo.Code.Once.IR.C_inl_56)
             C_iiv'45'inr_2808 -> coe MAlonzo.Code.Once.IR.C_id_22
             C_iiv'45'other_2816
               -> coe
                    MAlonzo.Code.Once.IR.C_case_70 (coe MAlonzo.Code.Once.IR.C_inl_56)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'inr_2808
        -> case coe v3 of
             C_iiv'45'inl_2802
               -> coe
                    MAlonzo.Code.Once.IR.C_case_70 (coe MAlonzo.Code.Once.IR.C_inr_62)
                    (coe MAlonzo.Code.Once.IR.C_inl_56)
             C_iiv'45'inr_2808
               -> coe
                    MAlonzo.Code.Once.IR.C_case_70 (coe MAlonzo.Code.Once.IR.C_inr_62)
                    (coe MAlonzo.Code.Once.IR.C_inr_62)
             C_iiv'45'other_2816
               -> coe
                    MAlonzo.Code.Once.IR.C_case_70 (coe MAlonzo.Code.Once.IR.C_inr_62)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'other_2816
        -> case coe v3 of
             C_iiv'45'inl_2802
               -> coe
                    MAlonzo.Code.Once.IR.C_case_70 v0
                    (coe MAlonzo.Code.Once.IR.C_inl_56)
             C_iiv'45'inr_2808
               -> coe
                    MAlonzo.Code.Once.IR.C_case_70 v0
                    (coe MAlonzo.Code.Once.IR.C_inr_62)
             C_iiv'45'other_2816 -> coe MAlonzo.Code.Once.IR.C_case_70 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_3716 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case_3716 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'case_3716 v3 v4
du_optimize'45'case_3716 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case_3716 v0 v1
  = coe
      du_optimize'45'case'45'aux_3672 (coe v0) (coe v1)
      (coe du_inlInrView_3280 (coe v0)) (coe du_inlInrView_3280 (coe v1))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_3726 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once'45'structural_3726 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe MAlonzo.Code.Once.IR.C_id_22
      MAlonzo.Code.Once.IR.C__'8728'__30 v4 v6 v7
        -> coe
             d_optimize'45'compose_3550 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_3732 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_3732 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_optimize'45'pair_3656
                    (coe d_optimize'45'once_3732 (coe v0) (coe v8) (coe v6))
                    (coe d_optimize'45'once_3732 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44 -> coe MAlonzo.Code.Once.IR.C_fst_44
      MAlonzo.Code.Once.IR.C_snd_50 -> coe MAlonzo.Code.Once.IR.C_snd_50
      MAlonzo.Code.Once.IR.C_inl_56
        -> let v5
                 = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_214
                     (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                             (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v0)))
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe
                              eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_irtyTag_202
                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                              (coe
                                 eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_irtyTag_202
                                    (coe MAlonzo.Code.Once.IRTy.C_Void_18)))))) in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then coe seq (coe v7) (coe MAlonzo.Code.Once.IR.C_initial_78)
                       else coe seq (coe v7) (coe MAlonzo.Code.Once.IR.C_inl_56)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_inr_62
        -> let v5
                 = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_214
                     (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                             (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v0)))
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe
                              eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_irtyTag_202
                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                              (coe
                                 eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_irtyTag_202
                                    (coe MAlonzo.Code.Once.IRTy.C_Void_18)))))) in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then coe seq (coe v7) (coe MAlonzo.Code.Once.IR.C_initial_78)
                       else coe seq (coe v7) (coe MAlonzo.Code.Once.IR.C_inr_62)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_case_70 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    du_optimize'45'case_3716
                    (coe d_optimize'45'once_3732 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_3732 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe MAlonzo.Code.Once.IR.C_terminal_74
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe MAlonzo.Code.Once.IR.C_initial_78
      MAlonzo.Code.Once.IR.C_curry_86 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_86
                    (d_optimize'45'once_3732
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe MAlonzo.Code.Once.IR.C_apply_92
      MAlonzo.Code.Once.IR.C_In_96 v4
        -> coe MAlonzo.Code.Once.IR.C_In_96 v4
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v4
        -> coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v4
      MAlonzo.Code.Once.IR.C_Cata_108 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           MAlonzo.Code.Once.IR.C_Cata_108 v4
                           (d_optimize'45'once_3732
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10)
                                    (coe v1)))
                              (coe v1) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    MAlonzo.Code.Once.IR.C_Para_114 v4
                    (d_optimize'45'once_3732
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v7)
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_118 v4
        -> coe MAlonzo.Code.Once.IR.C_Out_118 v4
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v4
        -> coe MAlonzo.Code.Once.IR.C_in'45'ν_122 v4
      MAlonzo.Code.Once.IR.C_Ana_128 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    MAlonzo.Code.Once.IR.C_Ana_128 v4
                    (d_optimize'45'once_3732
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Hylo_136 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_Hylo_136 v3 v5 v6
                    (d_optimize'45'once_3732
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_optimize'45'nt_3738 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Fuse_144 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_Fuse_144 v3 v5 v6
                    (d_optimize'45'once_3732
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_optimize'45'nt_3738 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v3 -> coe v2
      MAlonzo.Code.Once.IR.C_const_150 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_const_150 v4 v5
      MAlonzo.Code.Once.IR.C_SigOp_156 v3 v4 v5
        -> let v6
                 = d__'8799'Type__120
                     (coe v3) (coe MAlonzo.Code.Once.Type.C_Void_120) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_78)
                       else coe seq (coe v8) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-once
d_optimize'45'once_3732 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once_3732 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_214
              (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                      (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v1)))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe
                       eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v1))
                       (coe
                          MAlonzo.Code.Once.IRTy.d_irtyTag_202
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                       (coe
                          eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v1))
                          (coe
                             MAlonzo.Code.Once.IRTy.d_irtyTag_202
                             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (let v6
                              = d_has'45'effect'63'_3344
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2) in
                        coe
                          (if coe v6
                             then coe
                                    d_optimize'45'once'45'structural_3726 (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)
                             else coe MAlonzo.Code.Once.IR.C_terminal_74))
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_214
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     erased
                                     (\ v6 ->
                                        coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                          (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v0)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe
                                           eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v0))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_irtyTag_202
                                              (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                           (coe
                                              eqInt
                                              (coe MAlonzo.Code.Once.IRTy.d_irtyTag_202 (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_irtyTag_202
                                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))))) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_78)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              d_optimize'45'once'45'structural_3726 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-nt
d_optimize'45'nt_3738 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> MAlonzo.Code.Once.IR.T_NatTr_18
d_optimize'45'nt_3738 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_158 -> coe v2
      MAlonzo.Code.Once.IR.C_ntK_164 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_K_8 v7
                      -> coe
                           MAlonzo.Code.Once.IR.C_ntK_164
                           (d_optimize'45'once_3732 (coe v6) (coe v7) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_172 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_ntFst_172
                    (d_optimize'45'nt_3738 (coe v7) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_180 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_ntSnd_180
                    (d_optimize'45'nt_3738 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_188 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_ntCase_188
                    (d_optimize'45'nt_3738 (coe v8) (coe v1) (coe v6))
                    (d_optimize'45'nt_3738 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_196 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_ntInl_196
                    (d_optimize'45'nt_3738 (coe v0) (coe v7) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_204 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_ntInr_204
                    (d_optimize'45'nt_3738 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_212 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_ntPair_212
                    (d_optimize'45'nt_3738 (coe v0) (coe v8) (coe v6))
                    (d_optimize'45'nt_3738 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-n
d_optimize'45'n_3934 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'n_3934 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_3934 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_3732 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_3946 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize_3946 v0 v1
  = coe d_optimize'45'n_3934 (coe v0) (coe v1) (coe (10 :: Integer))
