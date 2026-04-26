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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Optimize._≟AllocMode_
d__'8799'AllocMode__8 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'AllocMode__8 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_Stack_8
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.IR.C_Stack_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.CCC.IR.C_Heap_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Heap_10
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.IR.C_Stack_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.CCC.IR.C_Heap_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟Functor_
d__'8799'Functor__14 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Functor__14 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v3
               -> coe
                    du_'8799'Functor'45'K'45'aux_320
                    (coe d__'8799'Type__126 (coe v2) (coe v3))
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
                    du_'8799'Functor'45''8853''45'aux_334
                    (coe d__'8799'Functor__14 (coe v2) (coe v4))
                    (coe d__'8799'Functor__14 (coe v3) (coe v5))
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
                    du_'8799'Functor'45''8855''45'aux_356
                    (coe d__'8799'Functor__14 (coe v2) (coe v4))
                    (coe d__'8799'Functor__14 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Type-*-aux
d_'8799'Type'45''42''45'aux_24 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Type'45''42''45'aux_24 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'Type'45''42''45'aux_24 v4 v5
du_'8799'Type'45''42''45'aux_24 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45''42''45'aux_24 v0 v1
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
d_'8799'Type'45''43''45'aux_46 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Type'45''43''45'aux_46 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'Type'45''43''45'aux_46 v4 v5
du_'8799'Type'45''43''45'aux_46 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45''43''45'aux_46 v0 v1
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
d_'8799'Type'45''8658''45'aux_72 ::
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
d_'8799'Type'45''8658''45'aux_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8799'Type'45''8658''45'aux_72 v6 v7 v8
du_'8799'Type'45''8658''45'aux_72 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45''8658''45'aux_72 v0 v1 v2
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
d_'8799'Type'45'μ'45'aux_106 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Type'45'μ'45'aux_106 ~v0 ~v1 v2
  = du_'8799'Type'45'μ'45'aux_106 v2
du_'8799'Type'45'μ'45'aux_106 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45'μ'45'aux_106 v0
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
d_'8799'Type'45'ν'45'aux_116 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Type'45'ν'45'aux_116 ~v0 ~v1 v2
  = du_'8799'Type'45'ν'45'aux_116 v2
du_'8799'Type'45'ν'45'aux_116 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Type'45'ν'45'aux_116 v0
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
d__'8799'Type__126 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Type__126 v0 v1
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
                    du_'8799'Type'45''42''45'aux_24
                    (coe d__'8799'Type__126 (coe v2) (coe v4))
                    (coe d__'8799'Type__126 (coe v3) (coe v5))
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
                    du_'8799'Type'45''43''45'aux_46
                    (coe d__'8799'Type__126 (coe v2) (coe v4))
                    (coe d__'8799'Type__126 (coe v3) (coe v5))
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
                    du_'8799'Type'45''8658''45'aux_72
                    (coe d__'8799'Type__126 (coe v2) (coe v5))
                    (coe MAlonzo.Code.Once.Type.d__'8799'k__96 (coe v3) (coe v6))
                    (coe d__'8799'Type__126 (coe v4) (coe v7))
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
                    du_'8799'Type'45'μ'45'aux_106
                    (coe d__'8799'Functor__14 (coe v2) (coe v3))
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
                    du_'8799'Type'45'ν'45'aux_116
                    (coe d__'8799'Functor__14 (coe v2) (coe v3))
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
d_'8799'Functor'45'K'45'aux_320 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Functor'45'K'45'aux_320 ~v0 ~v1 v2
  = du_'8799'Functor'45'K'45'aux_320 v2
du_'8799'Functor'45'K'45'aux_320 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Functor'45'K'45'aux_320 v0
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
d_'8799'Functor'45''8853''45'aux_334 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Functor'45''8853''45'aux_334 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'Functor'45''8853''45'aux_334 v4 v5
du_'8799'Functor'45''8853''45'aux_334 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Functor'45''8853''45'aux_334 v0 v1
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
d_'8799'Functor'45''8855''45'aux_356 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'Functor'45''8855''45'aux_356 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'Functor'45''8855''45'aux_356 v4 v5
du_'8799'Functor'45''8855''45'aux_356 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'Functor'45''8855''45'aux_356 v0 v1
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
d_IRHead_414 = ()
data T_IRHead_414
  = C_h'45'id_416 | C_h'45''8728'_418 |
    C_h'45''10216''44''10217'_420 | C_h'45'fst_422 | C_h'45'snd_424 |
    C_h'45'inl_426 | C_h'45'inr_428 | C_h'45'case_430 |
    C_h'45'terminal_432 | C_h'45'initial_434 | C_h'45'curry_436 |
    C_h'45'apply_438 | C_h'45'arr_440 | C_h'45'In_442 |
    C_h'45'out'45'μ_444 | C_h'45'Cata_446 | C_h'45'Para_448 |
    C_h'45'Out_450 | C_h'45'in'45'ν_452 | C_h'45'Ana_454 |
    C_h'45'Hylo_456 | C_h'45'Fuse_458 | C_h'45'free'45'heap_460 |
    C_h'45'SigOp_462
-- Once.Optimize.headTag
d_headTag_464 :: T_IRHead_414 -> Integer
d_headTag_464 v0
  = case coe v0 of
      C_h'45'id_416 -> coe (0 :: Integer)
      C_h'45''8728'_418 -> coe (1 :: Integer)
      C_h'45''10216''44''10217'_420 -> coe (2 :: Integer)
      C_h'45'fst_422 -> coe (3 :: Integer)
      C_h'45'snd_424 -> coe (4 :: Integer)
      C_h'45'inl_426 -> coe (5 :: Integer)
      C_h'45'inr_428 -> coe (6 :: Integer)
      C_h'45'case_430 -> coe (7 :: Integer)
      C_h'45'terminal_432 -> coe (8 :: Integer)
      C_h'45'initial_434 -> coe (9 :: Integer)
      C_h'45'curry_436 -> coe (10 :: Integer)
      C_h'45'apply_438 -> coe (11 :: Integer)
      C_h'45'arr_440 -> coe (12 :: Integer)
      C_h'45'In_442 -> coe (14 :: Integer)
      C_h'45'out'45'μ_444 -> coe (15 :: Integer)
      C_h'45'Cata_446 -> coe (16 :: Integer)
      C_h'45'Para_448 -> coe (17 :: Integer)
      C_h'45'Out_450 -> coe (18 :: Integer)
      C_h'45'in'45'ν_452 -> coe (19 :: Integer)
      C_h'45'Ana_454 -> coe (20 :: Integer)
      C_h'45'Hylo_456 -> coe (21 :: Integer)
      C_h'45'Fuse_458 -> coe (22 :: Integer)
      C_h'45'free'45'heap_460 -> coe (23 :: Integer)
      C_h'45'SigOp_462 -> coe (24 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.headTag-inj
d_headTag'45'inj_470 ::
  T_IRHead_414 ->
  T_IRHead_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_headTag'45'inj_470 = erased
-- Once.Optimize._≟IRHead_
d__'8799'IRHead__476 ::
  T_IRHead_414 ->
  T_IRHead_414 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRHead__476 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe d_headTag_464 (coe v0)))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    eqInt (coe d_headTag_464 (coe v0))
                    (coe d_headTag_464 (coe v1)))) in
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
d_ir'45'head_504 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_IRHead_414
d_ir'45'head_504 ~v0 ~v1 v2 = du_ir'45'head_504 v2
du_ir'45'head_504 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_IRHead_414
du_ir'45'head_504 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_16 -> coe C_h'45'id_416
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v2 v4 v5
        -> coe C_h'45''8728'_418
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v4 v5 v6
        -> coe C_h'45''10216''44''10217'_420
      MAlonzo.Code.Once.CCC.IR.C_fst_38 -> coe C_h'45'fst_422
      MAlonzo.Code.Once.CCC.IR.C_snd_44 -> coe C_h'45'snd_424
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v3 -> coe C_h'45'inl_426
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v3 -> coe C_h'45'inr_428
      MAlonzo.Code.Once.CCC.IR.C_case_64 v4 v5 -> coe C_h'45'case_430
      MAlonzo.Code.Once.CCC.IR.C_terminal_68 -> coe C_h'45'terminal_432
      MAlonzo.Code.Once.CCC.IR.C_initial_72 -> coe C_h'45'initial_434
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v5 v6 -> coe C_h'45'curry_436
      MAlonzo.Code.Once.CCC.IR.C_apply_90 -> coe C_h'45'apply_438
      MAlonzo.Code.Once.CCC.IR.C_arr_98 -> coe C_h'45'arr_440
      MAlonzo.Code.Once.CCC.IR.C_In_102 v2 v3 -> coe C_h'45'In_442
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v2
        -> coe C_h'45'out'45'μ_444
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v2 v4 -> coe C_h'45'Cata_446
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v2 v4 -> coe C_h'45'Para_448
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v2 -> coe C_h'45'Out_450
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v2 v3
        -> coe C_h'45'in'45'ν_452
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v2 v4 -> coe C_h'45'Ana_454
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v1 v3 v4 v6 v7
        -> coe C_h'45'Hylo_456
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v1 v3 v4 v6 v7
        -> coe C_h'45'Fuse_458
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v1
        -> coe C_h'45'free'45'heap_460
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v3 -> coe C_h'45'SigOp_462
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.subst₂-IR
d_subst'8322''45'IR_514 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_subst'8322''45'IR_514 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_subst'8322''45'IR_514 v6
du_subst'8322''45'IR_514 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_subst'8322''45'IR_514 v0 = coe v0
-- Once.Optimize.ir-head-subst₂
d_ir'45'head'45'subst'8322'_532 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'head'45'subst'8322'_532 = erased
-- Once.Optimize.head-mismatch-abs
d_head'45'mismatch'45'abs_550 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_head'45'mismatch'45'abs_550 = erased
-- Once.Optimize.cross-no
d_cross'45'no_580 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cross'45'no_580 = erased
-- Once.Optimize.≟IRH
d_'8799'IRH_608 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH_608 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_'8799'IRH_608 v0 v1 v2 v3 v4 v5
du_'8799'IRH_608 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH_608 v0 v1 v2 v3 v4 v5
  = coe
      du_'8799'IRH'45'aux_644 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
      (coe
         d__'8799'IRHead__476 (coe du_ir'45'head_504 (coe v4))
         (coe du_ir'45'head_504 (coe v5)))
-- Once.Optimize.≟IRH-diag
d_'8799'IRH'45'diag_626 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'diag_626 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_'8799'IRH'45'diag_626 v0 v1 v2 v3 v4 v5
du_'8799'IRH'45'diag_626 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'diag_626 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.CCC.IR.C_id_16
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v7 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v12 v14 v15
               -> coe
                    du_'8799'IRH'45''8728''45'aux_776 (coe v0) (coe v7) (coe v1)
                    (coe v9) (coe v10) (coe v14) (coe v15)
                    (coe d__'8799'Type__126 (coe v7) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v9 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v17 v18 v19
                      -> coe
                           du_'8799'IRH'45''10216''44''10217''45'aux_816
                           (coe
                              du_'8799'IRH_608 (coe v0) (coe v12) (coe v0) (coe v12) (coe v9)
                              (coe v17))
                           (coe
                              du_'8799'IRH_608 (coe v0) (coe v13) (coe v0) (coe v13) (coe v10)
                              (coe v18))
                           (coe d__'8799'AllocMode__8 (coe v11) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_38
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_snd_44
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v8
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C_inl_50 v11
               -> let v12 = d__'8799'AllocMode__8 (coe v8) (coe v11) in
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
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v8
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C_inr_56 v11
               -> let v12 = d__'8799'AllocMode__8 (coe v8) (coe v11) in
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
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_case_64 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_case_64 v16 v17
                      -> coe
                           du_'8799'IRH'45'case'45'aux_956
                           (coe
                              du_'8799'IRH_608 (coe v11) (coe v1) (coe v11) (coe v1) (coe v9)
                              (coe v16))
                           (coe
                              du_'8799'IRH_608 (coe v12) (coe v1) (coe v12) (coe v1) (coe v10)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_initial_72
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_curry_82 v19 v20
                      -> coe
                           du_'8799'IRH'45'curry'45'aux_1018
                           (coe
                              du_'8799'IRH_608
                              (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v12))
                              (coe v14)
                              (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v12))
                              (coe v14) (coe v10) (coe v19))
                           (coe d__'8799'AllocMode__8 (coe v11) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_90
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_arr_98
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_In_102 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v9
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_In_102 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                             -> let v14 = d__'8799'Functor__14 (coe v9) (coe v13) in
                                coe
                                  (case coe v14 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                       -> if coe v15
                                            then coe
                                                   seq (coe v16)
                                                   (let v17
                                                          = d__'8799'AllocMode__8
                                                              (coe v8) (coe v12) in
                                                    coe
                                                      (case coe v17 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                           -> if coe v18
                                                                then coe
                                                                       seq (coe v19)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v18)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased))
                                                                else coe
                                                                       seq (coe v19)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v18)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
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
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
               -> coe
                    seq (coe v5)
                    (case coe v2 of
                       MAlonzo.Code.Once.Type.C_μ'45'type_128 v9
                         -> let v10 = d__'8799'Functor__14 (coe v8) (coe v9) in
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
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v7 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Cata_112 v12 v14
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v15
                             -> let v16 = d__'8799'Functor__14 (coe v10) (coe v15) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                       -> if coe v17
                                            then coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = coe
                                                              du_'8799'IRH'45'aux_644
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                 (coe v10) (coe v1))
                                                              (coe v1)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                 (coe v10) (coe v1))
                                                              (coe v1) (coe v9) (coe v14)
                                                              (let v19
                                                                     = coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                         erased
                                                                         (\ v19 ->
                                                                            coe
                                                                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                              (coe
                                                                                 d_headTag_464
                                                                                 (coe
                                                                                    du_ir'45'head_504
                                                                                    (coe v9))))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe
                                                                               eqInt
                                                                               (coe
                                                                                  d_headTag_464
                                                                                  (coe
                                                                                     du_ir'45'head_504
                                                                                     (coe v9)))
                                                                               (coe
                                                                                  d_headTag_464
                                                                                  (coe
                                                                                     du_ir'45'head_504
                                                                                     (coe v14))))
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                               (coe
                                                                                  eqInt
                                                                                  (coe
                                                                                     d_headTag_464
                                                                                     (coe
                                                                                        du_ir'45'head_504
                                                                                        (coe v9)))
                                                                                  (coe
                                                                                     d_headTag_464
                                                                                     (coe
                                                                                        du_ir'45'head_504
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
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v7 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Para_118 v12 v14
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v15
                             -> let v16 = d__'8799'Functor__14 (coe v10) (coe v15) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                       -> if coe v17
                                            then coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = coe
                                                              du_'8799'IRH'45'aux_644
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                 (coe v10)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'42'__122
                                                                    (coe v0) (coe v1)))
                                                              (coe v1)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                 (coe v10)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'42'__122
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
                                                                                 d_headTag_464
                                                                                 (coe
                                                                                    du_ir'45'head_504
                                                                                    (coe v9))))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe
                                                                               eqInt
                                                                               (coe
                                                                                  d_headTag_464
                                                                                  (coe
                                                                                     du_ir'45'head_504
                                                                                     (coe v9)))
                                                                               (coe
                                                                                  d_headTag_464
                                                                                  (coe
                                                                                     du_ir'45'head_504
                                                                                     (coe v14))))
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                               (coe
                                                                                  eqInt
                                                                                  (coe
                                                                                     d_headTag_464
                                                                                     (coe
                                                                                        du_ir'45'head_504
                                                                                        (coe v9)))
                                                                                  (coe
                                                                                     d_headTag_464
                                                                                     (coe
                                                                                        du_ir'45'head_504
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
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v8
               -> coe
                    seq (coe v5)
                    (case coe v2 of
                       MAlonzo.Code.Once.Type.C_ν'45'type_130 v9
                         -> let v10 = d__'8799'Functor__14 (coe v8) (coe v9) in
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
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v9
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v13
                             -> let v14 = d__'8799'Functor__14 (coe v9) (coe v13) in
                                coe
                                  (case coe v14 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                       -> if coe v15
                                            then coe
                                                   seq (coe v16)
                                                   (let v17
                                                          = d__'8799'AllocMode__8
                                                              (coe v8) (coe v12) in
                                                    coe
                                                      (case coe v17 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                           -> if coe v18
                                                                then coe
                                                                       seq (coe v19)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v18)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased))
                                                                else coe
                                                                       seq (coe v19)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v18)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
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
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Ana_132 v12 v14
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v15
                             -> let v16 = d__'8799'Functor__14 (coe v10) (coe v15) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                       -> if coe v17
                                            then coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = coe
                                                              du_'8799'IRH'45'aux_644 (coe v0)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                 (coe v10) (coe v0))
                                                              (coe v0)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
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
                                                                                 d_headTag_464
                                                                                 (coe
                                                                                    du_ir'45'head_504
                                                                                    (coe v9))))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe
                                                                               eqInt
                                                                               (coe
                                                                                  d_headTag_464
                                                                                  (coe
                                                                                     du_ir'45'head_504
                                                                                     (coe v9)))
                                                                               (coe
                                                                                  d_headTag_464
                                                                                  (coe
                                                                                     du_ir'45'head_504
                                                                                     (coe v14))))
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                               (coe
                                                                                  eqInt
                                                                                  (coe
                                                                                     d_headTag_464
                                                                                     (coe
                                                                                        du_ir'45'head_504
                                                                                        (coe v9)))
                                                                                  (coe
                                                                                     d_headTag_464
                                                                                     (coe
                                                                                        du_ir'45'head_504
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
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v6 v8 v9 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v14 v16 v17 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v21
                             -> let v22 = d__'8799'Functor__14 (coe v13) (coe v21) in
                                coe
                                  (case coe v22 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                       -> if coe v23
                                            then coe
                                                   seq (coe v24)
                                                   (let v25
                                                          = d__'8799'Functor__14
                                                              (coe v6) (coe v14) in
                                                    coe
                                                      (case coe v25 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                           -> if coe v26
                                                                then coe
                                                                       seq (coe v27)
                                                                       (coe
                                                                          du_'8799'IRH'45'Hylo'45'inner_1086
                                                                          (coe
                                                                             du_'8799'IRH_608
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v6) (coe v1))
                                                                             (coe v1)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v6) (coe v1))
                                                                             (coe v1) (coe v11)
                                                                             (coe v19))
                                                                          (coe
                                                                             du_'8799'IRH_608
                                                                             (coe v0)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v6) (coe v0))
                                                                             (coe v0)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v6) (coe v0))
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
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v6 v8 v9 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v14 v16 v17 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v21
                             -> let v22 = d__'8799'Functor__14 (coe v13) (coe v21) in
                                coe
                                  (case coe v22 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                       -> if coe v23
                                            then coe
                                                   seq (coe v24)
                                                   (let v25
                                                          = d__'8799'Functor__14
                                                              (coe v6) (coe v14) in
                                                    coe
                                                      (case coe v25 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                           -> if coe v26
                                                                then coe
                                                                       seq (coe v27)
                                                                       (coe
                                                                          du_'8799'IRH'45'Fuse'45'inner_1146
                                                                          (coe
                                                                             du_'8799'IRH_608
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v6) (coe v1))
                                                                             (coe v1)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v6) (coe v1))
                                                                             (coe v1) (coe v11)
                                                                             (coe v19))
                                                                          (coe
                                                                             du_'8799'IRH_608
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v13) (coe v0))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v6) (coe v0))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v13) (coe v0))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v6) (coe v0))
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
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v6
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v7
               -> let v8
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v8 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ref'45'id_24 (coe v6)))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                               (coe
                                  eqInt
                                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ref'45'id_24 (coe v6))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_ref'45'id_24 (coe v7)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                  (coe
                                     eqInt
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_ref'45'id_24
                                        (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_ref'45'id_24
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
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v8
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v11
               -> let v12
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v12 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_276 (coe v8)))
                            (coe
                               MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                               (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                  (MAlonzo.Code.Once.CCC.SigOp.Info.d_name_276 (coe v8)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                  (MAlonzo.Code.Once.CCC.SigOp.Info.d_name_276 (coe v11)))) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                         -> if coe v13
                              then let v15
                                         = seq
                                             (coe v14)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v13)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                   erased)) in
                                   coe
                                     (case coe v15 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                          -> if coe v16
                                               then coe
                                                      seq (coe v17)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                            erased))
                                               else coe
                                                      seq (coe v17)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else (let v15
                                          = seq
                                              (coe v14)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                 (coe v13)
                                                 (coe
                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                    coe
                                      (case coe v15 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                           -> if coe v16
                                                then coe
                                                       seq (coe v17)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v16)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                             erased))
                                                else coe
                                                       seq (coe v17)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v16)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                         _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-aux
d_'8799'IRH'45'aux_644 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'aux_644 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_'8799'IRH'45'aux_644 v0 v1 v2 v3 v4 v5 v6
du_'8799'IRH'45'aux_644 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'aux_644 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       du_'8799'IRH'45'diag_626 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5))
             else coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v7)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟IR_
d__'8799'IR__682 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IR__682 v0 v1 v2 v3
  = coe
      du_'8799'IRH_608 (coe v0) (coe v1) (coe v0) (coe v1) (coe v2)
      (coe v3)
-- Once.Optimize.μ-inj
d_μ'45'inj_692 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_μ'45'inj_692 = erased
-- Once.Optimize.ν-inj
d_ν'45'inj_698 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ν'45'inj_698 = erased
-- Once.Optimize.≟IRH-∘-inner
d_'8799'IRH'45''8728''45'inner_714 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''8728''45'inner_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                   v8
  = du_'8799'IRH'45''8728''45'inner_714 v7 v8
du_'8799'IRH'45''8728''45'inner_714 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''8728''45'inner_714 v0 v1
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
d_'8799'IRH'45''8728''45'aux_776 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''8728''45'aux_776 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8799'IRH'45''8728''45'aux_776 v0 v1 v3 v4 v5 v6 v7 v8
du_'8799'IRH'45''8728''45'aux_776 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''8728''45'aux_776 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       du_'8799'IRH'45''8728''45'inner_714
                       (coe
                          du_'8799'IRH_608 (coe v1) (coe v2) (coe v1) (coe v2) (coe v3)
                          (coe v5))
                       (coe
                          du_'8799'IRH_608 (coe v0) (coe v1) (coe v0) (coe v1) (coe v4)
                          (coe v6)))
             else coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-⟨,⟩-aux
d_'8799'IRH'45''10216''44''10217''45'aux_816 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''10216''44''10217''45'aux_816 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_'8799'IRH'45''10216''44''10217''45'aux_816 v9 v10 v11
du_'8799'IRH'45''10216''44''10217''45'aux_816 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''10216''44''10217''45'aux_816 v0 v1 v2
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
-- Once.Optimize.≟IRH-case-aux
d_'8799'IRH'45'case'45'aux_956 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'case'45'aux_956 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_'8799'IRH'45'case'45'aux_956 v7 v8
du_'8799'IRH'45'case'45'aux_956 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'case'45'aux_956 v0 v1
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
d_'8799'IRH'45'curry'45'aux_1018 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'curry'45'aux_1018 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                 v9
  = du_'8799'IRH'45'curry'45'aux_1018 v8 v9
du_'8799'IRH'45'curry'45'aux_1018 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'curry'45'aux_1018 v0 v1
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
-- Once.Optimize.≟IRH-Hylo-inner
d_'8799'IRH'45'Hylo'45'inner_1086 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'Hylo'45'inner_1086 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 v11 v12
  = du_'8799'IRH'45'Hylo'45'inner_1086 v11 v12
du_'8799'IRH'45'Hylo'45'inner_1086 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'Hylo'45'inner_1086 v0 v1
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
d_'8799'IRH'45'Fuse'45'inner_1146 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'Fuse'45'inner_1146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 v11 v12
  = du_'8799'IRH'45'Fuse'45'inner_1146 v11 v12
du_'8799'IRH'45'Fuse'45'inner_1146 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'Fuse'45'inner_1146 v0 v1
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
-- Once.Optimize.dec-to-bool
d_dec'45'to'45'bool_2372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
d_dec'45'to'45'bool_2372 ~v0 ~v1 v2 = du_dec'45'to'45'bool_2372 v2
du_dec'45'to'45'bool_2372 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
du_dec'45'to'45'bool_2372 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe seq (coe v2) (coe v1)
             else coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-Void
d_is'45'Void_2374 :: MAlonzo.Code.Once.Type.T_Type_108 -> Bool
d_is'45'Void_2374 v0
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
d_isUnitType_2376 :: MAlonzo.Code.Once.Type.T_Type_108 -> Bool
d_isUnitType_2376 v0
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
d_isVoidType_2378 :: MAlonzo.Code.Once.Type.T_Type_108 -> Bool
d_isVoidType_2378 v0
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
d_is'45'fst'63'_2384 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
d_is'45'fst'63'_2384 ~v0 ~v1 v2 = du_is'45'fst'63'_2384 v2
du_is'45'fst'63'_2384 :: MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
du_is'45'fst'63'_2384 v0
  = coe
      du_dec'45'to'45'bool_2372
      (coe
         d__'8799'IRHead__476 (coe du_ir'45'head_504 (coe v0))
         (coe C_h'45'fst_422))
-- Once.Optimize.is-snd?
d_is'45'snd'63'_2392 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
d_is'45'snd'63'_2392 ~v0 ~v1 v2 = du_is'45'snd'63'_2392 v2
du_is'45'snd'63'_2392 :: MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
du_is'45'snd'63'_2392 v0
  = coe
      du_dec'45'to'45'bool_2372
      (coe
         d__'8799'IRHead__476 (coe du_ir'45'head_504 (coe v0))
         (coe C_h'45'snd_424))
-- Once.Optimize.is-terminal?
d_is'45'terminal'63'_2400 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
d_is'45'terminal'63'_2400 ~v0 ~v1 v2
  = du_is'45'terminal'63'_2400 v2
du_is'45'terminal'63'_2400 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
du_is'45'terminal'63'_2400 v0
  = coe
      du_dec'45'to'45'bool_2372
      (coe
         d__'8799'IRHead__476 (coe du_ir'45'head_504 (coe v0))
         (coe C_h'45'terminal_432))
-- Once.Optimize.safe-pair-distrib
d_safe'45'pair'45'distrib_2412 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
d_safe'45'pair'45'distrib_2412 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_safe'45'pair'45'distrib_2412 v4 v5
du_safe'45'pair'45'distrib_2412 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
du_safe'45'pair'45'distrib_2412 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe du_is'45'fst'63'_2384 (coe v0))
         (coe du_is'45'snd'63'_2392 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe du_is'45'snd'63'_2392 (coe v0))
            (coe du_is'45'fst'63'_2384 (coe v1)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe du_is'45'terminal'63'_2400 (coe v0))
            (coe du_is'45'terminal'63'_2400 (coe v1))))
-- Once.Optimize.wants-coprod
d_wants'45'coprod_2422 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
d_wants'45'coprod_2422 ~v0 ~v1 v2 = du_wants'45'coprod_2422 v2
du_wants'45'coprod_2422 :: MAlonzo.Code.Once.CCC.IR.T_IR_12 -> Bool
du_wants'45'coprod_2422 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         du_dec'45'to'45'bool_2372
         (coe
            d__'8799'IRHead__476 (coe du_ir'45'head_504 (coe v0))
            (coe C_h'45'case_430)))
      (coe
         du_dec'45'to'45'bool_2372
         (coe
            d__'8799'IRHead__476 (coe du_ir'45'head_504 (coe v0))
            (coe C_h'45'terminal_432)))
-- Once.Optimize.PairView
d_PairView_2432 a0 a1 a2 a3 = ()
data T_PairView_2432
  = C_is'45'pair_2446 | C_is'45'other'45'pair_2456
-- Once.Optimize.CoprodView
d_CoprodView_2464 a0 a1 a2 a3 = ()
data T_CoprodView_2464
  = C_is'45'inl_2472 | C_is'45'inr_2480 |
    C_is'45'other'45'coprod_2490
-- Once.Optimize.ComposeFirstView
d_ComposeFirstView_2496 a0 a1 a2 = ()
data T_ComposeFirstView_2496
  = C_cf'45'id_2500 | C_cf'45'terminal_2504 | C_cf'45'fst_2510 |
    C_cf'45'snd_2516 | C_cf'45'case_2528 | C_cf'45'other_2536
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_2542 a0 a1 a2 = ()
data T_ComposeSecondView_2542
  = C_cs'45'id_2546 | C_cs'45'initial_2550 | C_cs'45'other_2558
-- Once.Optimize.FstSndView
d_FstSndView_2564 a0 a1 a2 = ()
data T_FstSndView_2564
  = C_fsv'45'fst_2570 | C_fsv'45'snd_2576 | C_fsv'45'other_2584
-- Once.Optimize.InlInrView
d_InlInrView_2590 a0 a1 a2 = ()
data T_InlInrView_2590
  = C_iiv'45'inl_2598 | C_iiv'45'inr_2606 | C_iiv'45'other_2614
-- Once.Optimize.pairView-gen
d_pairView'45'gen_2628 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_2432
d_pairView'45'gen_2628 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_2628 v2
du_pairView'45'gen_2628 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_PairView_2432
du_pairView'45'gen_2628 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_16 -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v2 v4 v5
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v4 v5 v6
        -> coe C_is'45'pair_2446
      MAlonzo.Code.Once.CCC.IR.C_fst_38 -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_snd_44 -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v3
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v3
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_case_64 v4 v5
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_initial_72
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v5 v6
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_apply_90
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_arr_98 -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_In_102 v2 v3
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v2
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v2 v4
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v2 v4
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v2
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v2 v3
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v2 v4
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v1
        -> coe C_is'45'other'45'pair_2456
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v3
        -> coe C_is'45'other'45'pair_2456
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.pairView
d_pairView_2750 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_PairView_2432
d_pairView_2750 ~v0 ~v1 ~v2 v3 = du_pairView_2750 v3
du_pairView_2750 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_PairView_2432
du_pairView_2750 v0 = coe du_pairView'45'gen_2628 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_2766 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CoprodView_2464
d_coprodView'45'gen_2766 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_2766 v2
du_coprodView'45'gen_2766 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_CoprodView_2464
du_coprodView'45'gen_2766 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_16
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v2 v4 v5
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v4 v5 v6
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_fst_38
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_snd_44
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v3 -> coe C_is'45'inl_2472
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v3 -> coe C_is'45'inr_2480
      MAlonzo.Code.Once.CCC.IR.C_case_64 v4 v5
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_initial_72
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v5 v6
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_apply_90
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_arr_98
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_In_102 v2 v3
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v2
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v2 v4
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v2 v4
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v2
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v2 v3
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v2 v4
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v1
        -> coe C_is'45'other'45'coprod_2490
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v3
        -> coe C_is'45'other'45'coprod_2490
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.coprodView
d_coprodView_2886 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_CoprodView_2464
d_coprodView_2886 ~v0 ~v1 ~v2 v3 = du_coprodView_2886 v3
du_coprodView_2886 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_CoprodView_2464
du_coprodView_2886 v0 = coe du_coprodView'45'gen_2766 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_2896 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_ComposeFirstView_2496
d_composeFirstView_2896 ~v0 ~v1 v2 = du_composeFirstView_2896 v2
du_composeFirstView_2896 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_ComposeFirstView_2496
du_composeFirstView_2896 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_16 -> coe C_cf'45'id_2500
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v2 v4 v5
        -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v4 v5 v6
        -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_fst_38 -> coe C_cf'45'fst_2510
      MAlonzo.Code.Once.CCC.IR.C_snd_44 -> coe C_cf'45'snd_2516
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v3 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v3 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_case_64 v4 v5 -> coe C_cf'45'case_2528
      MAlonzo.Code.Once.CCC.IR.C_terminal_68 -> coe C_cf'45'terminal_2504
      MAlonzo.Code.Once.CCC.IR.C_initial_72 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v5 v6 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_apply_90 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_arr_98 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_In_102 v2 v3 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v2
        -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v2 v4 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v2 v4 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v2 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v2 v3
        -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v2 v4 -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v1 v3 v4 v6 v7
        -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v1 v3 v4 v6 v7
        -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v1
        -> coe C_cf'45'other_2536
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v3 -> coe C_cf'45'other_2536
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_2970 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_ComposeSecondView_2542
d_composeSecondView_2970 ~v0 ~v1 v2 = du_composeSecondView_2970 v2
du_composeSecondView_2970 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_ComposeSecondView_2542
du_composeSecondView_2970 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_16 -> coe C_cs'45'id_2546
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v2 v4 v5
        -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v4 v5 v6
        -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_fst_38 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_snd_44 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v3 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v3 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_case_64 v4 v5 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_terminal_68 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_initial_72 -> coe C_cs'45'initial_2550
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v5 v6 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_apply_90 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_arr_98 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_In_102 v2 v3 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v2
        -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v2 v4 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v2 v4 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v2 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v2 v3
        -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v2 v4 -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v1 v3 v4 v6 v7
        -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v1 v3 v4 v6 v7
        -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v1
        -> coe C_cs'45'other_2558
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v3 -> coe C_cs'45'other_2558
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_3044 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_FstSndView_2564
d_fstSndView_3044 ~v0 ~v1 v2 = du_fstSndView_3044 v2
du_fstSndView_3044 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_FstSndView_2564
du_fstSndView_3044 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_16 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v2 v4 v5
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v4 v5 v6
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_fst_38 -> coe C_fsv'45'fst_2570
      MAlonzo.Code.Once.CCC.IR.C_snd_44 -> coe C_fsv'45'snd_2576
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v3 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v3 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_case_64 v4 v5 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_terminal_68 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_initial_72 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v5 v6
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_apply_90 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_arr_98 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_In_102 v2 v3 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v2
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v2 v4
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v2 v4
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v2 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v2 v3
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v2 v4 -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v1 v3 v4 v6 v7
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v1 v3 v4 v6 v7
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v1
        -> coe C_fsv'45'other_2584
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v3 -> coe C_fsv'45'other_2584
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_3118 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_InlInrView_2590
d_inlInrView_3118 ~v0 ~v1 v2 = du_inlInrView_3118 v2
du_inlInrView_3118 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> T_InlInrView_2590
du_inlInrView_3118 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_16 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v2 v4 v5
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v4 v5 v6
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_fst_38 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_snd_44 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v3 -> coe C_iiv'45'inl_2598
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v3 -> coe C_iiv'45'inr_2606
      MAlonzo.Code.Once.CCC.IR.C_case_64 v4 v5 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_terminal_68 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_initial_72 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v5 v6
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_apply_90 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_arr_98 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_In_102 v2 v3 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v2
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v2 v4
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v2 v4
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v2 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v2 v3
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v2 v4 -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v1 v3 v4 v6 v7
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v1 v3 v4 v6 v7
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v1
        -> coe C_iiv'45'other_2614
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v3 -> coe C_iiv'45'other_2614
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-fst
d_optimize'45'fst_3192 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'fst_3192 ~v0 v1 v2 v3
  = du_optimize'45'fst_3192 v1 v2 v3
du_optimize'45'fst_3192 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_optimize'45'fst_3192 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_2628 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_2446
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v13 v14 v15
                  -> coe v13
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_2456
           -> coe
                MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.CCC.IR.C_fst_38) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-snd
d_optimize'45'snd_3214 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'snd_3214 ~v0 v1 v2 v3
  = du_optimize'45'snd_3214 v1 v2 v3
du_optimize'45'snd_3214 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_optimize'45'snd_3214 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_2628 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_2446
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v13 v14 v15
                  -> coe v14
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_2456
           -> coe
                MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.CCC.IR.C_snd_44) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_3238 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'post'45'case_3238 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_3238 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_3238 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_optimize'45'post'45'case_3238 v0 v1 v2 v3 v4
  = let v5 = coe du_coprodView'45'gen_2766 (coe v4) in
    coe
      (case coe v5 of
         C_is'45'inl_2472 -> coe v2
         C_is'45'inr_2480 -> coe v3
         C_is'45'other'45'coprod_2490
           -> coe
                MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.CCC.IR.C_case_64 v2 v3) v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_3308 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'compose'45'second_3308 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_3308 v1 v3 v4
du_optimize'45'compose'45'second_3308 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_optimize'45'compose'45'second_3308 v0 v1 v2
  = let v3 = coe du_composeSecondView_2970 (coe v2) in
    coe
      (case coe v3 of
         C_cs'45'id_2546 -> coe v1
         C_cs'45'initial_2550 -> coe MAlonzo.Code.Once.CCC.IR.C_initial_72
         C_cs'45'other_2558
           -> coe MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v0 v1 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose
d_optimize'45'compose_3338 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'compose_3338 ~v0 v1 v2 v3 v4
  = du_optimize'45'compose_3338 v1 v2 v3 v4
du_optimize'45'compose_3338 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_optimize'45'compose_3338 v0 v1 v2 v3
  = let v4 = coe du_composeFirstView_2896 (coe v2) in
    coe
      (case coe v4 of
         C_cf'45'id_2500 -> coe v3
         C_cf'45'terminal_2504 -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_68
         C_cf'45'fst_2510
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
                  -> coe du_optimize'45'fst_3192 (coe v1) (coe v8) (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError
         C_cf'45'snd_2516
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
                  -> coe du_optimize'45'snd_3214 (coe v7) (coe v1) (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError
         C_cf'45'case_2528
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Once.CCC.IR.C_case_64 v15 v16
                         -> coe
                              du_optimize'45'post'45'case_3238 (coe v10) (coe v11) (coe v15)
                              (coe v16) (coe v3)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         C_cf'45'other_2536
           -> coe
                du_optimize'45'compose'45'second_3308 (coe v0) (coe v2) (coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-pair-aux
d_optimize'45'pair'45'aux_3388 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  T_FstSndView_2564 ->
  T_FstSndView_2564 -> MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'pair'45'aux_3388 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'pair'45'aux_3388 v3 v4 v5 v6
du_optimize'45'pair'45'aux_3388 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  T_FstSndView_2564 ->
  T_FstSndView_2564 -> MAlonzo.Code.Once.CCC.IR.T_IR_12
du_optimize'45'pair'45'aux_3388 v0 v1 v2 v3
  = case coe v2 of
      C_fsv'45'fst_2570
        -> case coe v3 of
             C_fsv'45'fst_2570
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_38)
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_38)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_8)
             C_fsv'45'snd_2576 -> coe MAlonzo.Code.Once.CCC.IR.C_id_16
             C_fsv'45'other_2584
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_38) v1
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'snd_2576
        -> case coe v3 of
             C_fsv'45'fst_2570
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_44)
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_38)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_8)
             C_fsv'45'snd_2576
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_44)
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_44)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_8)
             C_fsv'45'other_2584
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_44) v1
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'other_2584
        -> case coe v3 of
             C_fsv'45'fst_2570
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v0
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_38)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_8)
             C_fsv'45'snd_2576
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v0
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_44)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_8)
             C_fsv'45'other_2584
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v0 v1
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_3432 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'pair_3432 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'pair_3432 v3 v4
du_optimize'45'pair_3432 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_optimize'45'pair_3432 v0 v1
  = coe
      du_optimize'45'pair'45'aux_3388 (coe v0) (coe v1)
      (coe du_fstSndView_3044 (coe v0)) (coe du_fstSndView_3044 (coe v1))
-- Once.Optimize.optimize-case-aux
d_optimize'45'case'45'aux_3448 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  T_InlInrView_2590 ->
  T_InlInrView_2590 -> MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'case'45'aux_3448 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'case'45'aux_3448 v3 v4 v5 v6
du_optimize'45'case'45'aux_3448 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  T_InlInrView_2590 ->
  T_InlInrView_2590 -> MAlonzo.Code.Once.CCC.IR.T_IR_12
du_optimize'45'case'45'aux_3448 v0 v1 v2 v3
  = case coe v2 of
      C_iiv'45'inl_2598
        -> case coe v0 of
             MAlonzo.Code.Once.CCC.IR.C_inl_50 v9
               -> case coe v3 of
                    C_iiv'45'inl_2598
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.IR.C_inl_50 v15
                             -> coe
                                  MAlonzo.Code.Once.CCC.IR.C_case_64
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inl_50 v9)
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inl_50 v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_iiv'45'inr_2606 -> coe MAlonzo.Code.Once.CCC.IR.C_id_16
                    C_iiv'45'other_2614
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_case_64
                           (coe MAlonzo.Code.Once.CCC.IR.C_inl_50 v9) v1
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'inr_2606
        -> case coe v0 of
             MAlonzo.Code.Once.CCC.IR.C_inr_56 v9
               -> case coe v3 of
                    C_iiv'45'inl_2598
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.IR.C_inl_50 v15
                             -> coe
                                  MAlonzo.Code.Once.CCC.IR.C_case_64
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inr_56 v9)
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inl_50 v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_iiv'45'inr_2606
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.IR.C_inr_56 v15
                             -> coe
                                  MAlonzo.Code.Once.CCC.IR.C_case_64
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inr_56 v9)
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inr_56 v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_iiv'45'other_2614
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_case_64
                           (coe MAlonzo.Code.Once.CCC.IR.C_inr_56 v9) v1
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'other_2614
        -> case coe v3 of
             C_iiv'45'inl_2598
               -> case coe v1 of
                    MAlonzo.Code.Once.CCC.IR.C_inl_50 v12
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_case_64 v0
                           (coe MAlonzo.Code.Once.CCC.IR.C_inl_50 v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_iiv'45'inr_2606
               -> case coe v1 of
                    MAlonzo.Code.Once.CCC.IR.C_inr_56 v12
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_case_64 v0
                           (coe MAlonzo.Code.Once.CCC.IR.C_inr_56 v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_iiv'45'other_2614 -> coe MAlonzo.Code.Once.CCC.IR.C_case_64 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_3492 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'case_3492 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'case_3492 v3 v4
du_optimize'45'case_3492 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_optimize'45'case_3492 v0 v1
  = coe
      du_optimize'45'case'45'aux_3448 (coe v0) (coe v1)
      (coe du_inlInrView_3118 (coe v0)) (coe du_inlInrView_3118 (coe v1))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_3502 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'once'45'structural_3502 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_16
        -> coe MAlonzo.Code.Once.CCC.IR.C_id_16
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v4 v6 v7
        -> coe
             du_optimize'45'compose_3338 (coe v4) (coe v1)
             (coe d_optimize'45'once_3508 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_3508 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__122 v9 v10
               -> coe
                    du_optimize'45'pair_3432
                    (coe d_optimize'45'once_3508 (coe v0) (coe v9) (coe v6))
                    (coe d_optimize'45'once_3508 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_38
        -> coe MAlonzo.Code.Once.CCC.IR.C_fst_38
      MAlonzo.Code.Once.CCC.IR.C_snd_44
        -> coe MAlonzo.Code.Once.CCC.IR.C_snd_44
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v5
        -> let v6
                 = d__'8799'Type__126
                     (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_120) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_initial_72)
                       else coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_inl_50 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v5
        -> let v6
                 = d__'8799'Type__126
                     (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_120) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_initial_72)
                       else coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_inr_56 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.IR.C_case_64 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
               -> coe
                    du_optimize'45'case_3492
                    (coe d_optimize'45'once_3508 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_3508 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_68
      MAlonzo.Code.Once.CCC.IR.C_initial_72
        -> coe MAlonzo.Code.Once.CCC.IR.C_initial_72
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_82
                    (d_optimize'45'once_3508
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v9))
                       (coe v11) (coe v7))
                    v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_90
        -> coe MAlonzo.Code.Once.CCC.IR.C_apply_90
      MAlonzo.Code.Once.CCC.IR.C_arr_98
        -> coe MAlonzo.Code.Once.CCC.IR.C_arr_98
      MAlonzo.Code.Once.CCC.IR.C_In_102 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_In_102 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v4
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Cata_112 v4
                    (d_optimize'45'once_3508
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v7) (coe v1))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Para_118 v4
                    (d_optimize'45'once_3508
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_Out_122 v4
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Ana_132 v4
                    (d_optimize'45'once_3508
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v3 v5 v6 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v3 v5 v6
             (d_optimize'45'once_3508
                (coe
                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v3) (coe v1))
                (coe v1) (coe v8))
             (d_optimize'45'once_3508
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v3) (coe v0))
                (coe v9))
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v3 v5 v6
                    (d_optimize'45'once_3508
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_optimize'45'once_3508
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v10) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v3) (coe v0))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v3 -> coe v2
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v5
        -> let v6
                 = d__'8799'Type__126
                     (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_120) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_initial_72)
                       else coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_SigOp_156 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-once
d_optimize'45'once_3508 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'once_3508 v0 v1 v2
  = let v3
          = d__'8799'Type__126
              (coe v1) (coe MAlonzo.Code.Once.Type.C_Unit_118) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe MAlonzo.Code.Once.CCC.IR.C_terminal_68)
                else coe
                       seq (coe v5)
                       (let v6
                              = d__'8799'Type__126
                                  (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_120) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe
                                           seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_initial_72)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              d_optimize'45'once'45'structural_3502 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-n
d_optimize'45'n_3684 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize'45'n_3684 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_3684 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_3508 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_3696 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_optimize_3696 v0 v1
  = coe d_optimize'45'n_3684 (coe v0) (coe v1) (coe (10 :: Integer))
