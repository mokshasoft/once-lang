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
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Optimize._≟AllocMode_
d__'8799'AllocMode__8 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'AllocMode__8 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_Stack_260
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.IR.C_Stack_260
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.CCC.IR.C_Heap_262
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Heap_262
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.IR.C_Stack_260
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.CCC.IR.C_Heap_262
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟Functor_
d__'8799'Functor__14 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Functor__14 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_114 v3
               -> coe
                    du_'8799'Functor'45'K'45'aux_320
                    (coe d__'8799'Type__126 (coe v2) (coe v3))
             MAlonzo.Code.Once.Type.C_Id_116
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__118 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__120 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Id_116
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_114 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_116
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'8853'__118 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__120 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8853'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_114 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_116
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__118 v4 v5
               -> coe
                    du_'8799'Functor'45''8853''45'aux_334
                    (coe d__'8799'Functor__14 (coe v2) (coe v4))
                    (coe d__'8799'Functor__14 (coe v3) (coe v5))
             MAlonzo.Code.Once.Type.C__'8855'__120 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_114 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_116
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__118 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__120 v4 v5
               -> coe
                    du_'8799'Functor'45''8855''45'aux_356
                    (coe d__'8799'Functor__14 (coe v2) (coe v4))
                    (coe d__'8799'Functor__14 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Type-*-aux
d_'8799'Type'45''42''45'aux_24 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
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
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
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
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
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
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Type__126 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_122
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Void_124
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v4 v5
               -> coe
                    du_'8799'Type'45''42''45'aux_24
                    (coe d__'8799'Type__126 (coe v2) (coe v4))
                    (coe d__'8799'Type__126 (coe v3) (coe v5))
             MAlonzo.Code.Once.Type.C__'43'__128 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v4 v5
               -> coe
                    du_'8799'Type'45''43''45'aux_46
                    (coe d__'8799'Type__126 (coe v2) (coe v4))
                    (coe d__'8799'Type__126 (coe v3) (coe v5))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v5 v6 v7
               -> coe
                    du_'8799'Type'45''8658''45'aux_72
                    (coe d__'8799'Type__126 (coe v2) (coe v5))
                    (coe MAlonzo.Code.Once.Type.d__'8799'k__100 (coe v3) (coe v6))
                    (coe d__'8799'Type__126 (coe v4) (coe v7))
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v3
               -> coe
                    du_'8799'Type'45'μ'45'aux_106
                    (coe d__'8799'Functor__14 (coe v2) (coe v3))
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v3
               -> coe
                    du_'8799'Type'45'ν'45'aux_116
                    (coe d__'8799'Functor__14 (coe v2) (coe v3))
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_136
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Float_138
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Str_140
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Buffer_142
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_124
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_140
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_142
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟Functor-K-aux
d_'8799'Functor'45'K'45'aux_320 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
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
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
    C_h'45'SigOp_462 | C_h'45'const_464
-- Once.Optimize.headTag
d_headTag_466 :: T_IRHead_414 -> Integer
d_headTag_466 v0
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
      C_h'45'const_464 -> coe (25 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.headTag-inj
d_headTag'45'inj_472 ::
  T_IRHead_414 ->
  T_IRHead_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_headTag'45'inj_472 = erased
-- Once.Optimize._≟IRHead_
d__'8799'IRHead__478 ::
  T_IRHead_414 ->
  T_IRHead_414 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRHead__478 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe d_headTag_466 (coe v0)))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    eqInt (coe d_headTag_466 (coe v0))
                    (coe d_headTag_466 (coe v1)))) in
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
d_ir'45'head_506 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_IRHead_414
d_ir'45'head_506 ~v0 ~v1 v2 = du_ir'45'head_506 v2
du_ir'45'head_506 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_IRHead_414
du_ir'45'head_506 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_280 -> coe C_h'45'id_416
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v2 v4 v5
        -> coe C_h'45''8728'_418
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v4 v5 v6
        -> coe C_h'45''10216''44''10217'_420
      MAlonzo.Code.Once.CCC.IR.C_fst_302 -> coe C_h'45'fst_422
      MAlonzo.Code.Once.CCC.IR.C_snd_308 -> coe C_h'45'snd_424
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v3 -> coe C_h'45'inl_426
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v3 -> coe C_h'45'inr_428
      MAlonzo.Code.Once.CCC.IR.C_case_328 v4 v5 -> coe C_h'45'case_430
      MAlonzo.Code.Once.CCC.IR.C_terminal_332 -> coe C_h'45'terminal_432
      MAlonzo.Code.Once.CCC.IR.C_initial_336 -> coe C_h'45'initial_434
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v5 v6 -> coe C_h'45'curry_436
      MAlonzo.Code.Once.CCC.IR.C_apply_354 -> coe C_h'45'apply_438
      MAlonzo.Code.Once.CCC.IR.C_arr_362 -> coe C_h'45'arr_440
      MAlonzo.Code.Once.CCC.IR.C_In_366 v2 v3 -> coe C_h'45'In_442
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v2
        -> coe C_h'45'out'45'μ_444
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v2 v4 -> coe C_h'45'Cata_446
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v2 v4 -> coe C_h'45'Para_448
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v2 -> coe C_h'45'Out_450
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v2 v3
        -> coe C_h'45'in'45'ν_452
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v2 v4 -> coe C_h'45'Ana_454
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v1 v3 v4 v6 v7
        -> coe C_h'45'Hylo_456
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v1 v3 v4 v6 v7
        -> coe C_h'45'Fuse_458
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v1
        -> coe C_h'45'free'45'heap_460
      MAlonzo.Code.Once.CCC.IR.C_const_418 v2 v3 v4
        -> coe C_h'45'const_464
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v3 -> coe C_h'45'SigOp_462
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.subst₂-IR
d_subst'8322''45'IR_516 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_subst'8322''45'IR_516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_subst'8322''45'IR_516 v6
du_subst'8322''45'IR_516 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_subst'8322''45'IR_516 v0 = coe v0
-- Once.Optimize.ir-head-subst₂
d_ir'45'head'45'subst'8322'_534 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'head'45'subst'8322'_534 = erased
-- Once.Optimize.head-mismatch-abs
d_head'45'mismatch'45'abs_552 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_head'45'mismatch'45'abs_552 = erased
-- Once.Optimize.cross-no
d_cross'45'no_582 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cross'45'no_582 = erased
-- Once.Optimize.≟IRH
d_'8799'IRH_610 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH_610 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_'8799'IRH_610 v0 v1 v2 v3 v4 v5
du_'8799'IRH_610 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH_610 v0 v1 v2 v3 v4 v5
  = coe
      du_'8799'IRH'45'aux_646 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
      (coe
         d__'8799'IRHead__478 (coe du_ir'45'head_506 (coe v4))
         (coe du_ir'45'head_506 (coe v5)))
-- Once.Optimize.≟IRH-diag
d_'8799'IRH'45'diag_628 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'diag_628 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_'8799'IRH'45'diag_628 v0 v1 v2 v3 v4 v5
du_'8799'IRH'45'diag_628 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'diag_628 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.CCC.IR.C_id_280
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v7 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v12 v14 v15
               -> coe
                    du_'8799'IRH'45''8728''45'aux_1020 (coe v0) (coe v7) (coe v1)
                    (coe v9) (coe v10) (coe v14) (coe v15)
                    (coe d__'8799'Type__126 (coe v7) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v9 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v17 v18 v19
                      -> coe
                           du_'8799'IRH'45''10216''44''10217''45'aux_1060
                           (coe
                              du_'8799'IRH_610 (coe v0) (coe v12) (coe v0) (coe v12) (coe v9)
                              (coe v17))
                           (coe
                              du_'8799'IRH_610 (coe v0) (coe v13) (coe v0) (coe v13) (coe v10)
                              (coe v18))
                           (coe d__'8799'AllocMode__8 (coe v11) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_302
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_snd_308
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v8
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C_inl_314 v11
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
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v8
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C_inr_320 v11
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
      MAlonzo.Code.Once.CCC.IR.C_case_328 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_case_328 v16 v17
                      -> coe
                           du_'8799'IRH'45'case'45'aux_1200
                           (coe
                              du_'8799'IRH_610 (coe v11) (coe v1) (coe v11) (coe v1) (coe v9)
                              (coe v16))
                           (coe
                              du_'8799'IRH_610 (coe v12) (coe v1) (coe v12) (coe v1) (coe v10)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_332
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_initial_336
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_curry_346 v19 v20
                      -> coe
                           du_'8799'IRH'45'curry'45'aux_1262
                           (coe
                              du_'8799'IRH_610
                              (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v12))
                              (coe v14)
                              (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v12))
                              (coe v14) (coe v10) (coe v19))
                           (coe d__'8799'AllocMode__8 (coe v11) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_354
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_arr_362
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_In_366 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v9
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_In_366 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_132 v13
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
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v8
               -> coe
                    seq (coe v5)
                    (case coe v2 of
                       MAlonzo.Code.Once.Type.C_μ'45'type_132 v9
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
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v7 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Cata_376 v12 v14
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_132 v15
                             -> let v16 = d__'8799'Functor__14 (coe v10) (coe v15) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                       -> if coe v17
                                            then coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = coe
                                                              du_'8799'IRH'45'aux_646
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                 (coe v10) (coe v1))
                                                              (coe v1)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
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
                                                                                 d_headTag_466
                                                                                 (coe
                                                                                    du_ir'45'head_506
                                                                                    (coe v9))))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe
                                                                               eqInt
                                                                               (coe
                                                                                  d_headTag_466
                                                                                  (coe
                                                                                     du_ir'45'head_506
                                                                                     (coe v9)))
                                                                               (coe
                                                                                  d_headTag_466
                                                                                  (coe
                                                                                     du_ir'45'head_506
                                                                                     (coe v14))))
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                               (coe
                                                                                  eqInt
                                                                                  (coe
                                                                                     d_headTag_466
                                                                                     (coe
                                                                                        du_ir'45'head_506
                                                                                        (coe v9)))
                                                                                  (coe
                                                                                     d_headTag_466
                                                                                     (coe
                                                                                        du_ir'45'head_506
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
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v7 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Para_382 v12 v14
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_132 v15
                             -> let v16 = d__'8799'Functor__14 (coe v10) (coe v15) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                       -> if coe v17
                                            then coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = coe
                                                              du_'8799'IRH'45'aux_646
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                 (coe v10)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'42'__126
                                                                    (coe v0) (coe v1)))
                                                              (coe v1)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                 (coe v10)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'42'__126
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
                                                                                 d_headTag_466
                                                                                 (coe
                                                                                    du_ir'45'head_506
                                                                                    (coe v9))))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe
                                                                               eqInt
                                                                               (coe
                                                                                  d_headTag_466
                                                                                  (coe
                                                                                     du_ir'45'head_506
                                                                                     (coe v9)))
                                                                               (coe
                                                                                  d_headTag_466
                                                                                  (coe
                                                                                     du_ir'45'head_506
                                                                                     (coe v14))))
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                               (coe
                                                                                  eqInt
                                                                                  (coe
                                                                                     d_headTag_466
                                                                                     (coe
                                                                                        du_ir'45'head_506
                                                                                        (coe v9)))
                                                                                  (coe
                                                                                     d_headTag_466
                                                                                     (coe
                                                                                        du_ir'45'head_506
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
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v8
               -> coe
                    seq (coe v5)
                    (case coe v2 of
                       MAlonzo.Code.Once.Type.C_ν'45'type_134 v9
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
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v9
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_134 v13
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
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Ana_396 v12 v14
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_134 v15
                             -> let v16 = d__'8799'Functor__14 (coe v10) (coe v15) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                       -> if coe v17
                                            then coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = coe
                                                              du_'8799'IRH'45'aux_646 (coe v0)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                 (coe v10) (coe v0))
                                                              (coe v0)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
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
                                                                                 d_headTag_466
                                                                                 (coe
                                                                                    du_ir'45'head_506
                                                                                    (coe v9))))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe
                                                                               eqInt
                                                                               (coe
                                                                                  d_headTag_466
                                                                                  (coe
                                                                                     du_ir'45'head_506
                                                                                     (coe v9)))
                                                                               (coe
                                                                                  d_headTag_466
                                                                                  (coe
                                                                                     du_ir'45'head_506
                                                                                     (coe v14))))
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                               (coe
                                                                                  eqInt
                                                                                  (coe
                                                                                     d_headTag_466
                                                                                     (coe
                                                                                        du_ir'45'head_506
                                                                                        (coe v9)))
                                                                                  (coe
                                                                                     d_headTag_466
                                                                                     (coe
                                                                                        du_ir'45'head_506
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
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v6 v8 v9 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v14 v16 v17 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_132 v21
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
                                                                          du_'8799'IRH'45'Hylo'45'inner_1330
                                                                          (coe
                                                                             du_'8799'IRH_610
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                                (coe v6) (coe v1))
                                                                             (coe v1)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                                (coe v6) (coe v1))
                                                                             (coe v1) (coe v11)
                                                                             (coe v19))
                                                                          (coe
                                                                             d__'8799'NatTr__704
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
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v6 v8 v9 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v14 v16 v17 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_132 v21
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
                                                                          du_'8799'IRH'45'Fuse'45'inner_1390
                                                                          (coe
                                                                             du_'8799'IRH_610
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                                (coe v6) (coe v1))
                                                                             (coe v1)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                                (coe v6) (coe v1))
                                                                             (coe v1) (coe v11)
                                                                             (coe v19))
                                                                          (coe
                                                                             d__'8799'NatTr__704
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
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v6
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v7
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
      MAlonzo.Code.Once.CCC.IR.C_const_418 v7 v8 v9
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C_const_418 v11 v12 v13
               -> coe
                    d_'8799'const'45'irrelevant_2892 v1 v7 v8 v9 v11 v12 v13 erased v7
                    v11 v8 v12 v9 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v8
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v11
               -> let v12
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v12 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_162 (coe v8)))
                            (coe
                               MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                               (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                  (MAlonzo.Code.Once.CCC.SigOp.Info.d_name_162 (coe v8)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                  (MAlonzo.Code.Once.CCC.SigOp.Info.d_name_162 (coe v11)))) in
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
d_'8799'IRH'45'aux_646 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'aux_646 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_'8799'IRH'45'aux_646 v0 v1 v2 v3 v4 v5 v6
du_'8799'IRH'45'aux_646 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'aux_646 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       du_'8799'IRH'45'diag_628 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5))
             else coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v7)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟IR_
d__'8799'IR__684 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IR__684 v0 v1 v2 v3
  = coe
      du_'8799'IRH_610 (coe v0) (coe v1) (coe v0) (coe v1) (coe v2)
      (coe v3)
-- Once.Optimize.nt-headTag
d_nt'45'headTag_694 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 -> Integer
d_nt'45'headTag_694 ~v0 ~v1 v2 = du_nt'45'headTag_694 v2
du_nt'45'headTag_694 ::
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 -> Integer
du_nt'45'headTag_694 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_426 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_ntK_432 v3 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_ntFst_440 v4 -> coe (2 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_448 v4 -> coe (3 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_ntCase_456 v4 v5 -> coe (4 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_ntInl_464 v4 -> coe (5 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_ntInr_472 v4 -> coe (6 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_ntPair_480 v4 v5 -> coe (7 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟NatTr_
d__'8799'NatTr__704 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'NatTr__704 v0 v1 v2 v3
  = coe
      d_'8799'NatTr'45'aux_714 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe du_nt'45'headTag_694 (coe v2))
         (coe du_nt'45'headTag_694 (coe v3)))
-- Once.Optimize.≟NatTr-aux
d_'8799'NatTr'45'aux_714 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'NatTr'45'aux_714 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       du_'8799'NatTr'45'diag_724 (coe v0) (coe v1) (coe v2) (coe v3))
             else coe
                    seq (coe v6)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v5)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟NatTr-diag
d_'8799'NatTr'45'diag_724 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'NatTr'45'diag_724 v0 v1 v2 v3 ~v4
  = du_'8799'NatTr'45'diag_724 v0 v1 v2 v3
du_'8799'NatTr'45'diag_724 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'NatTr'45'diag_724 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_426
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.CCC.IR.C_ntK_432 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v7
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v8
                      -> case coe v3 of
                           MAlonzo.Code.Once.CCC.IR.C_ntK_432 v11
                             -> let v12
                                      = coe
                                          du_'8799'IRH'45'aux_646 (coe v7) (coe v8) (coe v7)
                                          (coe v8) (coe v6) (coe v11)
                                          (let v12
                                                 = coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                     erased
                                                     (\ v12 ->
                                                        coe
                                                          MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                          (coe
                                                             d_headTag_466
                                                             (coe du_ir'45'head_506 (coe v6))))
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                        (coe
                                                           eqInt
                                                           (coe
                                                              d_headTag_466
                                                              (coe du_ir'45'head_506 (coe v6)))
                                                           (coe
                                                              d_headTag_466
                                                              (coe du_ir'45'head_506 (coe v11))))
                                                        (coe
                                                           MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                           (coe
                                                              eqInt
                                                              (coe
                                                                 d_headTag_466
                                                                 (coe du_ir'45'head_506 (coe v6)))
                                                              (coe
                                                                 d_headTag_466
                                                                 (coe
                                                                    du_ir'45'head_506
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
      MAlonzo.Code.Once.CCC.IR.C_ntFst_440 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Once.CCC.IR.C_ntFst_440 v13
                      -> let v14
                               = d_'8799'NatTr'45'aux_714
                                   (coe v8) (coe v1) (coe v7) (coe v13)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_694 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_694 (coe v7))
                                            (coe du_nt'45'headTag_694 (coe v13)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_694 (coe v7))
                                               (coe du_nt'45'headTag_694 (coe v13)))))) in
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
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_448 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Once.CCC.IR.C_ntSnd_448 v13
                      -> let v14
                               = d_'8799'NatTr'45'aux_714
                                   (coe v9) (coe v1) (coe v7) (coe v13)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_694 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_694 (coe v7))
                                            (coe du_nt'45'headTag_694 (coe v13)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_694 (coe v7))
                                               (coe du_nt'45'headTag_694 (coe v13)))))) in
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
      MAlonzo.Code.Once.CCC.IR.C_ntCase_456 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Once.CCC.IR.C_ntCase_456 v14 v15
                      -> let v16
                               = d_'8799'NatTr'45'aux_714
                                   (coe v9) (coe v1) (coe v7) (coe v14)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v16 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_694 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_694 (coe v7))
                                            (coe du_nt'45'headTag_694 (coe v14)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_694 (coe v7))
                                               (coe du_nt'45'headTag_694 (coe v14)))))) in
                         coe
                           (let v17
                                  = d_'8799'NatTr'45'aux_714
                                      (coe v10) (coe v1) (coe v8) (coe v15)
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v17 ->
                                            coe
                                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                              (coe du_nt'45'headTag_694 (coe v8)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe
                                               eqInt (coe du_nt'45'headTag_694 (coe v8))
                                               (coe du_nt'45'headTag_694 (coe v15)))
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                               (coe
                                                  eqInt (coe du_nt'45'headTag_694 (coe v8))
                                                  (coe du_nt'45'headTag_694 (coe v15)))))) in
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
      MAlonzo.Code.Once.CCC.IR.C_ntInl_464 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Once.CCC.IR.C_ntInl_464 v13
                      -> let v14
                               = d_'8799'NatTr'45'aux_714
                                   (coe v0) (coe v8) (coe v7) (coe v13)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_694 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_694 (coe v7))
                                            (coe du_nt'45'headTag_694 (coe v13)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_694 (coe v7))
                                               (coe du_nt'45'headTag_694 (coe v13)))))) in
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
      MAlonzo.Code.Once.CCC.IR.C_ntInr_472 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Once.CCC.IR.C_ntInr_472 v13
                      -> let v14
                               = d_'8799'NatTr'45'aux_714
                                   (coe v0) (coe v9) (coe v7) (coe v13)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_694 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_694 (coe v7))
                                            (coe du_nt'45'headTag_694 (coe v13)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_694 (coe v7))
                                               (coe du_nt'45'headTag_694 (coe v13)))))) in
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
      MAlonzo.Code.Once.CCC.IR.C_ntPair_480 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Once.CCC.IR.C_ntPair_480 v14 v15
                      -> let v16
                               = d_'8799'NatTr'45'aux_714
                                   (coe v0) (coe v9) (coe v7) (coe v14)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v16 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                           (coe du_nt'45'headTag_694 (coe v7)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                         (coe
                                            eqInt (coe du_nt'45'headTag_694 (coe v7))
                                            (coe du_nt'45'headTag_694 (coe v14)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                            (coe
                                               eqInt (coe du_nt'45'headTag_694 (coe v7))
                                               (coe du_nt'45'headTag_694 (coe v14)))))) in
                         coe
                           (let v17
                                  = d_'8799'NatTr'45'aux_714
                                      (coe v0) (coe v10) (coe v8) (coe v15)
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v17 ->
                                            coe
                                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                              (coe du_nt'45'headTag_694 (coe v8)))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe
                                               eqInt (coe du_nt'45'headTag_694 (coe v8))
                                               (coe du_nt'45'headTag_694 (coe v15)))
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                               (coe
                                                  eqInt (coe du_nt'45'headTag_694 (coe v8))
                                                  (coe du_nt'45'headTag_694 (coe v15)))))) in
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
d_μ'45'inj_936 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_μ'45'inj_936 = erased
-- Once.Optimize.ν-inj
d_ν'45'inj_942 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ν'45'inj_942 = erased
-- Once.Optimize.≟IRH-∘-inner
d_'8799'IRH'45''8728''45'inner_958 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''8728''45'inner_958 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                   v8
  = du_'8799'IRH'45''8728''45'inner_958 v7 v8
du_'8799'IRH'45''8728''45'inner_958 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''8728''45'inner_958 v0 v1
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
d_'8799'IRH'45''8728''45'aux_1020 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''8728''45'aux_1020 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8799'IRH'45''8728''45'aux_1020 v0 v1 v3 v4 v5 v6 v7 v8
du_'8799'IRH'45''8728''45'aux_1020 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''8728''45'aux_1020 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       du_'8799'IRH'45''8728''45'inner_958
                       (coe
                          du_'8799'IRH_610 (coe v1) (coe v2) (coe v1) (coe v2) (coe v3)
                          (coe v5))
                       (coe
                          du_'8799'IRH_610 (coe v0) (coe v1) (coe v0) (coe v1) (coe v4)
                          (coe v6)))
             else coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-⟨,⟩-aux
d_'8799'IRH'45''10216''44''10217''45'aux_1060 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''10216''44''10217''45'aux_1060 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_'8799'IRH'45''10216''44''10217''45'aux_1060 v9 v10 v11
du_'8799'IRH'45''10216''44''10217''45'aux_1060 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''10216''44''10217''45'aux_1060 v0 v1 v2
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
d_'8799'IRH'45'case'45'aux_1200 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
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
d_'8799'IRH'45'curry'45'aux_1262 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'curry'45'aux_1262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                 v9
  = du_'8799'IRH'45'curry'45'aux_1262 v8 v9
du_'8799'IRH'45'curry'45'aux_1262 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'curry'45'aux_1262 v0 v1
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
d_'8799'IRH'45'Hylo'45'inner_1330 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'Hylo'45'inner_1330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 v11 v12
  = du_'8799'IRH'45'Hylo'45'inner_1330 v11 v12
du_'8799'IRH'45'Hylo'45'inner_1330 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'Hylo'45'inner_1330 v0 v1
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
d_'8799'IRH'45'Fuse'45'inner_1390 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'Fuse'45'inner_1390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 v11 v12
  = du_'8799'IRH'45'Fuse'45'inner_1390 v11 v12
du_'8799'IRH'45'Fuse'45'inner_1390 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'Fuse'45'inner_1390 v0 v1
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
-- Once.Optimize._.I.⟦_⟧
d_'10214'_'10215'_2746 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_2746 = erased
-- Once.Optimize._.M.⟦_⟧
d_'10214'_'10215'_2872 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_2872 = erased
-- Once.Optimize._.≟const-irrelevant
d_'8799'const'45'irrelevant_2892
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Optimize._.\8799const-irrelevant"
-- Once.Optimize.dec-to-bool
d_dec'45'to'45'bool_2898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
d_dec'45'to'45'bool_2898 ~v0 ~v1 v2 = du_dec'45'to'45'bool_2898 v2
du_dec'45'to'45'bool_2898 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
du_dec'45'to'45'bool_2898 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe seq (coe v2) (coe v1)
             else coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-Void
d_is'45'Void_2900 :: MAlonzo.Code.Once.Type.T_Type_112 -> Bool
d_is'45'Void_2900 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_122
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Void_124
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C__'42'__126 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'43'__128 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Int_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_138
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Str_140
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Buffer_142
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isUnitType
d_isUnitType_2902 :: MAlonzo.Code.Once.Type.T_Type_112 -> Bool
d_isUnitType_2902 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_122
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C_Void_124
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'42'__126 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'43'__128 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Int_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_138
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Str_140
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Buffer_142
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isVoidType
d_isVoidType_2904 :: MAlonzo.Code.Once.Type.T_Type_112 -> Bool
d_isVoidType_2904 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_122
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Void_124
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C__'42'__126 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'43'__128 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Int_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_138
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Str_140
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Buffer_142
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-fst?
d_is'45'fst'63'_2910 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
d_is'45'fst'63'_2910 ~v0 ~v1 v2 = du_is'45'fst'63'_2910 v2
du_is'45'fst'63'_2910 :: MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
du_is'45'fst'63'_2910 v0
  = coe
      du_dec'45'to'45'bool_2898
      (coe
         d__'8799'IRHead__478 (coe du_ir'45'head_506 (coe v0))
         (coe C_h'45'fst_422))
-- Once.Optimize.is-snd?
d_is'45'snd'63'_2918 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
d_is'45'snd'63'_2918 ~v0 ~v1 v2 = du_is'45'snd'63'_2918 v2
du_is'45'snd'63'_2918 :: MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
du_is'45'snd'63'_2918 v0
  = coe
      du_dec'45'to'45'bool_2898
      (coe
         d__'8799'IRHead__478 (coe du_ir'45'head_506 (coe v0))
         (coe C_h'45'snd_424))
-- Once.Optimize.is-terminal?
d_is'45'terminal'63'_2926 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
d_is'45'terminal'63'_2926 ~v0 ~v1 v2
  = du_is'45'terminal'63'_2926 v2
du_is'45'terminal'63'_2926 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
du_is'45'terminal'63'_2926 v0
  = coe
      du_dec'45'to'45'bool_2898
      (coe
         d__'8799'IRHead__478 (coe du_ir'45'head_506 (coe v0))
         (coe C_h'45'terminal_432))
-- Once.Optimize.safe-pair-distrib
d_safe'45'pair'45'distrib_2938 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
d_safe'45'pair'45'distrib_2938 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_safe'45'pair'45'distrib_2938 v4 v5
du_safe'45'pair'45'distrib_2938 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
du_safe'45'pair'45'distrib_2938 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe du_is'45'fst'63'_2910 (coe v0))
         (coe du_is'45'snd'63'_2918 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe du_is'45'snd'63'_2918 (coe v0))
            (coe du_is'45'fst'63'_2910 (coe v1)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe du_is'45'terminal'63'_2926 (coe v0))
            (coe du_is'45'terminal'63'_2926 (coe v1))))
-- Once.Optimize.wants-coprod
d_wants'45'coprod_2948 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
d_wants'45'coprod_2948 ~v0 ~v1 v2 = du_wants'45'coprod_2948 v2
du_wants'45'coprod_2948 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
du_wants'45'coprod_2948 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         du_dec'45'to'45'bool_2898
         (coe
            d__'8799'IRHead__478 (coe du_ir'45'head_506 (coe v0))
            (coe C_h'45'case_430)))
      (coe
         du_dec'45'to'45'bool_2898
         (coe
            d__'8799'IRHead__478 (coe du_ir'45'head_506 (coe v0))
            (coe C_h'45'terminal_432)))
-- Once.Optimize.PairView
d_PairView_2958 a0 a1 a2 a3 = ()
data T_PairView_2958
  = C_is'45'pair_2972 | C_is'45'other'45'pair_2982
-- Once.Optimize.CoprodView
d_CoprodView_2990 a0 a1 a2 a3 = ()
data T_CoprodView_2990
  = C_is'45'inl_2998 | C_is'45'inr_3006 |
    C_is'45'other'45'coprod_3016
-- Once.Optimize.ComposeFirstView
d_ComposeFirstView_3022 a0 a1 a2 = ()
data T_ComposeFirstView_3022
  = C_cf'45'id_3026 | C_cf'45'terminal_3030 | C_cf'45'fst_3036 |
    C_cf'45'snd_3042 | C_cf'45'case_3054 | C_cf'45'other_3062
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_3068 a0 a1 a2 = ()
data T_ComposeSecondView_3068
  = C_cs'45'id_3072 | C_cs'45'initial_3076 | C_cs'45'other_3084
-- Once.Optimize.FstSndView
d_FstSndView_3090 a0 a1 a2 = ()
data T_FstSndView_3090
  = C_fsv'45'fst_3096 | C_fsv'45'snd_3102 | C_fsv'45'other_3110
-- Once.Optimize.InlInrView
d_InlInrView_3116 a0 a1 a2 = ()
data T_InlInrView_3116
  = C_iiv'45'inl_3124 | C_iiv'45'inr_3132 | C_iiv'45'other_3140
-- Once.Optimize.pairView-gen
d_pairView'45'gen_3154 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_2958
d_pairView'45'gen_3154 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_3154 v2
du_pairView'45'gen_3154 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_PairView_2958
du_pairView'45'gen_3154 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_280 -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v2 v4 v5
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v4 v5 v6
        -> coe C_is'45'pair_2972
      MAlonzo.Code.Once.CCC.IR.C_fst_302
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_snd_308
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v3
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v3
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_case_328 v4 v5
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_terminal_332
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_initial_336
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v5 v6
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_apply_354
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_arr_362
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_In_366 v2 v3
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v2
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v2 v4
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v2 v4
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v2
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v2 v3
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v2 v4
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v1
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_const_418 v2 v3 v4
        -> coe C_is'45'other'45'pair_2982
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v3
        -> coe C_is'45'other'45'pair_2982
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.pairView
d_pairView_3284 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_PairView_2958
d_pairView_3284 ~v0 ~v1 ~v2 v3 = du_pairView_3284 v3
du_pairView_3284 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_PairView_2958
du_pairView_3284 v0 = coe du_pairView'45'gen_3154 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_3300 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CoprodView_2990
d_coprodView'45'gen_3300 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_3300 v2
du_coprodView'45'gen_3300 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_CoprodView_2990
du_coprodView'45'gen_3300 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_280
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v2 v4 v5
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v4 v5 v6
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_fst_302
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_snd_308
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v3 -> coe C_is'45'inl_2998
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v3 -> coe C_is'45'inr_3006
      MAlonzo.Code.Once.CCC.IR.C_case_328 v4 v5
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_terminal_332
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_initial_336
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v5 v6
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_apply_354
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_arr_362
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_In_366 v2 v3
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v2
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v2 v4
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v2 v4
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v2
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v2 v3
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v2 v4
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v1 v3 v4 v6 v7
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v1
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_const_418 v2 v3 v4
        -> coe C_is'45'other'45'coprod_3016
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v3
        -> coe C_is'45'other'45'coprod_3016
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.coprodView
d_coprodView_3428 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_CoprodView_2990
d_coprodView_3428 ~v0 ~v1 ~v2 v3 = du_coprodView_3428 v3
du_coprodView_3428 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_CoprodView_2990
du_coprodView_3428 v0 = coe du_coprodView'45'gen_3300 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_3438 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_ComposeFirstView_3022
d_composeFirstView_3438 ~v0 ~v1 v2 = du_composeFirstView_3438 v2
du_composeFirstView_3438 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_ComposeFirstView_3022
du_composeFirstView_3438 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_280 -> coe C_cf'45'id_3026
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v2 v4 v5
        -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v4 v5 v6
        -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_fst_302 -> coe C_cf'45'fst_3036
      MAlonzo.Code.Once.CCC.IR.C_snd_308 -> coe C_cf'45'snd_3042
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v3 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v3 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_case_328 v4 v5 -> coe C_cf'45'case_3054
      MAlonzo.Code.Once.CCC.IR.C_terminal_332
        -> coe C_cf'45'terminal_3030
      MAlonzo.Code.Once.CCC.IR.C_initial_336 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v5 v6
        -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_apply_354 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_arr_362 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_In_366 v2 v3 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v2
        -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v2 v4 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v2 v4 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v2 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v2 v3
        -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v2 v4 -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v1 v3 v4 v6 v7
        -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v1 v3 v4 v6 v7
        -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v1
        -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_const_418 v2 v3 v4
        -> coe C_cf'45'other_3062
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v3 -> coe C_cf'45'other_3062
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_3518 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_ComposeSecondView_3068
d_composeSecondView_3518 ~v0 ~v1 v2 = du_composeSecondView_3518 v2
du_composeSecondView_3518 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_ComposeSecondView_3068
du_composeSecondView_3518 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_280 -> coe C_cs'45'id_3072
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v2 v4 v5
        -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v4 v5 v6
        -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_fst_302 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_snd_308 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v3 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v3 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_case_328 v4 v5 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_terminal_332 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_initial_336 -> coe C_cs'45'initial_3076
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v5 v6
        -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_apply_354 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_arr_362 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_In_366 v2 v3 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v2
        -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v2 v4 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v2 v4 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v2 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v2 v3
        -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v2 v4 -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v1 v3 v4 v6 v7
        -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v1 v3 v4 v6 v7
        -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v1
        -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_const_418 v2 v3 v4
        -> coe C_cs'45'other_3084
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v3 -> coe C_cs'45'other_3084
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_3598 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_FstSndView_3090
d_fstSndView_3598 ~v0 ~v1 v2 = du_fstSndView_3598 v2
du_fstSndView_3598 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_FstSndView_3090
du_fstSndView_3598 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_280 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v2 v4 v5
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v4 v5 v6
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_fst_302 -> coe C_fsv'45'fst_3096
      MAlonzo.Code.Once.CCC.IR.C_snd_308 -> coe C_fsv'45'snd_3102
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v3 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v3 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_case_328 v4 v5
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_terminal_332 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_initial_336 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v5 v6
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_apply_354 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_arr_362 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_In_366 v2 v3 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v2
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v2 v4
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v2 v4
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v2 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v2 v3
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v2 v4 -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v1 v3 v4 v6 v7
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v1 v3 v4 v6 v7
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v1
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_const_418 v2 v3 v4
        -> coe C_fsv'45'other_3110
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v3 -> coe C_fsv'45'other_3110
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_3678 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_InlInrView_3116
d_inlInrView_3678 ~v0 ~v1 v2 = du_inlInrView_3678 v2
du_inlInrView_3678 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> T_InlInrView_3116
du_inlInrView_3678 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.IR.C_id_280 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v2 v4 v5
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v4 v5 v6
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_fst_302 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_snd_308 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v3 -> coe C_iiv'45'inl_3124
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v3 -> coe C_iiv'45'inr_3132
      MAlonzo.Code.Once.CCC.IR.C_case_328 v4 v5
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_terminal_332 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_initial_336 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v5 v6
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_apply_354 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_arr_362 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_In_366 v2 v3 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v2
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v2 v4
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v2 v4
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v2 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v2 v3
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v2 v4 -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v1 v3 v4 v6 v7
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v1 v3 v4 v6 v7
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v1
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_const_418 v2 v3 v4
        -> coe C_iiv'45'other_3140
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v3 -> coe C_iiv'45'other_3140
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?
d_has'45'effect'63'_3756 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
d_has'45'effect'63'_3756 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_280
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'effect'63'_3756 (coe v4) (coe v1) (coe v6))
             (coe d_has'45'effect'63'_3756 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_3756 (coe v0) (coe v9) (coe v6))
                    (coe d_has'45'effect'63'_3756 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_302
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_snd_308
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_case_328 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_3756 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63'_3756 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_332
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_initial_336
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
               -> coe
                    d_has'45'effect'63'_3756
                    (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v9))
                    (coe v11) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_354
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.CCC.IR.C_arr_362
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_In_366 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    d_has'45'effect'63'_3756
                    (coe
                       MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v1))
                    (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    d_has'45'effect'63'_3756
                    (coe
                       MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7)
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                    (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    d_has'45'effect'63'_3756 (coe v0)
                    (coe
                       MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v0))
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe
                       d_has'45'effect'63'_3756
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (coe d_has'45'effect'63''45'nt_3762 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe
                       d_has'45'effect'63'_3756
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (coe d_has'45'effect'63''45'nt_3762 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.CCC.IR.C_const_418 v4 v5 v6
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?-nt
d_has'45'effect'63''45'nt_3762 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 -> Bool
d_has'45'effect'63''45'nt_3762 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_426
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.IR.C_ntK_432 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v7
                      -> coe d_has'45'effect'63'_3756 (coe v6) (coe v7) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntFst_440 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe d_has'45'effect'63''45'nt_3762 (coe v7) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_448 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe d_has'45'effect'63''45'nt_3762 (coe v8) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntCase_456 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63''45'nt_3762 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63''45'nt_3762 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInl_464 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe d_has'45'effect'63''45'nt_3762 (coe v0) (coe v7) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInr_472 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe d_has'45'effect'63''45'nt_3762 (coe v0) (coe v8) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntPair_480 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63''45'nt_3762 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63''45'nt_3762 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-fst
d_optimize'45'fst_3816 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'fst_3816 ~v0 v1 v2 v3
  = du_optimize'45'fst_3816 v1 v2 v3
du_optimize'45'fst_3816 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_optimize'45'fst_3816 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_3154 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_2972
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v13 v14 v15
                  -> coe v13
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_2982
           -> coe
                MAlonzo.Code.Once.CCC.IR.C__'8728'__288
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.CCC.IR.C_fst_302) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-snd
d_optimize'45'snd_3838 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'snd_3838 ~v0 v1 v2 v3
  = du_optimize'45'snd_3838 v1 v2 v3
du_optimize'45'snd_3838 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_optimize'45'snd_3838 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_3154 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_2972
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v13 v14 v15
                  -> coe v14
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_2982
           -> coe
                MAlonzo.Code.Once.CCC.IR.C__'8728'__288
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.CCC.IR.C_snd_308) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_3862 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'post'45'case_3862 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_3862 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_3862 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_optimize'45'post'45'case_3862 v0 v1 v2 v3 v4
  = let v5 = coe du_coprodView'45'gen_3300 (coe v4) in
    coe
      (case coe v5 of
         C_is'45'inl_2998 -> coe v2
         C_is'45'inr_3006 -> coe v3
         C_is'45'other'45'coprod_3016
           -> coe
                MAlonzo.Code.Once.CCC.IR.C__'8728'__288
                (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.CCC.IR.C_case_328 v2 v3) v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_3932 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'compose'45'second_3932 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_3932 v1 v3 v4
du_optimize'45'compose'45'second_3932 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_optimize'45'compose'45'second_3932 v0 v1 v2
  = let v3 = coe du_composeSecondView_3518 (coe v2) in
    coe
      (case coe v3 of
         C_cs'45'id_3072 -> coe v1
         C_cs'45'initial_3076 -> coe MAlonzo.Code.Once.CCC.IR.C_initial_336
         C_cs'45'other_3084
           -> coe MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v0 v1 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose
d_optimize'45'compose_3962 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'compose_3962 v0 v1 v2 v3 v4
  = let v5 = d_has'45'effect'63'_3756 (coe v0) (coe v1) (coe v4) in
    coe
      (if coe v5
         then coe MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v1 v3 v4
         else (let v6 = coe du_composeFirstView_3438 (coe v3) in
               coe
                 (case coe v6 of
                    C_cf'45'id_3026 -> coe v4
                    C_cf'45'terminal_3030
                      -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_332
                    C_cf'45'fst_3036
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
                             -> coe du_optimize'45'fst_3816 (coe v2) (coe v10) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'snd_3042
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
                             -> coe du_optimize'45'snd_3838 (coe v9) (coe v2) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'case_3054
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'43'__128 v12 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Once.CCC.IR.C_case_328 v17 v18
                                    -> coe
                                         du_optimize'45'post'45'case_3862 (coe v12) (coe v13)
                                         (coe v17) (coe v18) (coe v4)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'other_3062
                      -> coe
                           du_optimize'45'compose'45'second_3932 (coe v1) (coe v3) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Optimize.optimize-pair-aux
d_optimize'45'pair'45'aux_4024 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  T_FstSndView_3090 ->
  T_FstSndView_3090 -> MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'pair'45'aux_4024 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'pair'45'aux_4024 v3 v4 v5 v6
du_optimize'45'pair'45'aux_4024 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  T_FstSndView_3090 ->
  T_FstSndView_3090 -> MAlonzo.Code.Once.CCC.IR.T_IR_274
du_optimize'45'pair'45'aux_4024 v0 v1 v2 v3
  = case coe v2 of
      C_fsv'45'fst_3096
        -> case coe v3 of
             C_fsv'45'fst_3096
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_302)
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_302)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260)
             C_fsv'45'snd_3102 -> coe MAlonzo.Code.Once.CCC.IR.C_id_280
             C_fsv'45'other_3110
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_302) v1
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'snd_3102
        -> case coe v3 of
             C_fsv'45'fst_3096
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_308)
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_302)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260)
             C_fsv'45'snd_3102
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_308)
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_308)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260)
             C_fsv'45'other_3110
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_308) v1
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'other_3110
        -> case coe v3 of
             C_fsv'45'fst_3096
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v0
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_302)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260)
             C_fsv'45'snd_3102
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v0
                    (coe MAlonzo.Code.Once.CCC.IR.C_snd_308)
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260)
             C_fsv'45'other_3110
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v0 v1
                    (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_4068 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'pair_4068 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'pair_4068 v3 v4
du_optimize'45'pair_4068 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_optimize'45'pair_4068 v0 v1
  = coe
      du_optimize'45'pair'45'aux_4024 (coe v0) (coe v1)
      (coe du_fstSndView_3598 (coe v0)) (coe du_fstSndView_3598 (coe v1))
-- Once.Optimize.optimize-case-aux
d_optimize'45'case'45'aux_4084 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  T_InlInrView_3116 ->
  T_InlInrView_3116 -> MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'case'45'aux_4084 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'case'45'aux_4084 v3 v4 v5 v6
du_optimize'45'case'45'aux_4084 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  T_InlInrView_3116 ->
  T_InlInrView_3116 -> MAlonzo.Code.Once.CCC.IR.T_IR_274
du_optimize'45'case'45'aux_4084 v0 v1 v2 v3
  = case coe v2 of
      C_iiv'45'inl_3124
        -> case coe v0 of
             MAlonzo.Code.Once.CCC.IR.C_inl_314 v9
               -> case coe v3 of
                    C_iiv'45'inl_3124
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.IR.C_inl_314 v15
                             -> coe
                                  MAlonzo.Code.Once.CCC.IR.C_case_328
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inl_314 v9)
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inl_314 v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_iiv'45'inr_3132 -> coe MAlonzo.Code.Once.CCC.IR.C_id_280
                    C_iiv'45'other_3140
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_case_328
                           (coe MAlonzo.Code.Once.CCC.IR.C_inl_314 v9) v1
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'inr_3132
        -> case coe v0 of
             MAlonzo.Code.Once.CCC.IR.C_inr_320 v9
               -> case coe v3 of
                    C_iiv'45'inl_3124
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.IR.C_inl_314 v15
                             -> coe
                                  MAlonzo.Code.Once.CCC.IR.C_case_328
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inr_320 v9)
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inl_314 v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_iiv'45'inr_3132
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.IR.C_inr_320 v15
                             -> coe
                                  MAlonzo.Code.Once.CCC.IR.C_case_328
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inr_320 v9)
                                  (coe MAlonzo.Code.Once.CCC.IR.C_inr_320 v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_iiv'45'other_3140
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_case_328
                           (coe MAlonzo.Code.Once.CCC.IR.C_inr_320 v9) v1
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'other_3140
        -> case coe v3 of
             C_iiv'45'inl_3124
               -> case coe v1 of
                    MAlonzo.Code.Once.CCC.IR.C_inl_314 v12
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_case_328 v0
                           (coe MAlonzo.Code.Once.CCC.IR.C_inl_314 v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_iiv'45'inr_3132
               -> case coe v1 of
                    MAlonzo.Code.Once.CCC.IR.C_inr_320 v12
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_case_328 v0
                           (coe MAlonzo.Code.Once.CCC.IR.C_inr_320 v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_iiv'45'other_3140
               -> coe MAlonzo.Code.Once.CCC.IR.C_case_328 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_4128 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'case_4128 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'case_4128 v3 v4
du_optimize'45'case_4128 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_optimize'45'case_4128 v0 v1
  = coe
      du_optimize'45'case'45'aux_4084 (coe v0) (coe v1)
      (coe du_inlInrView_3678 (coe v0)) (coe du_inlInrView_3678 (coe v1))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_4138 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'once'45'structural_4138 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_280
        -> coe MAlonzo.Code.Once.CCC.IR.C_id_280
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v4 v6 v7
        -> coe
             d_optimize'45'compose_3962 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_4144 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_4144 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
               -> coe
                    du_optimize'45'pair_4068
                    (coe d_optimize'45'once_4144 (coe v0) (coe v9) (coe v6))
                    (coe d_optimize'45'once_4144 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_302
        -> coe MAlonzo.Code.Once.CCC.IR.C_fst_302
      MAlonzo.Code.Once.CCC.IR.C_snd_308
        -> coe MAlonzo.Code.Once.CCC.IR.C_snd_308
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v5
        -> let v6
                 = d__'8799'Type__126
                     (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_124) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_initial_336)
                       else coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_inl_314 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v5
        -> let v6
                 = d__'8799'Type__126
                     (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_124) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_initial_336)
                       else coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_inr_320 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.IR.C_case_328 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
               -> coe
                    du_optimize'45'case_4128
                    (coe d_optimize'45'once_4144 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_4144 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_332
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_332
      MAlonzo.Code.Once.CCC.IR.C_initial_336
        -> coe MAlonzo.Code.Once.CCC.IR.C_initial_336
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_346
                    (d_optimize'45'once_4144
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v9))
                       (coe v11) (coe v7))
                    v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_354
        -> coe MAlonzo.Code.Once.CCC.IR.C_apply_354
      MAlonzo.Code.Once.CCC.IR.C_arr_362
        -> coe MAlonzo.Code.Once.CCC.IR.C_arr_362
      MAlonzo.Code.Once.CCC.IR.C_In_366 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_In_366 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v4
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Cata_376 v4
                    (d_optimize'45'once_4144
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v1))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Para_382 v4
                    (d_optimize'45'once_4144
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_Out_386 v4
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Ana_396 v4
                    (d_optimize'45'once_4144
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v3 v5 v6
                    (d_optimize'45'once_4144
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_optimize'45'nt_4150 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v3 v5 v6
                    (d_optimize'45'once_4144
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_optimize'45'nt_4150 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v3 -> coe v2
      MAlonzo.Code.Once.CCC.IR.C_const_418 v4 v5 v6
        -> coe MAlonzo.Code.Once.CCC.IR.C_const_418 v4 v5 v6
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v5
        -> let v6
                 = d__'8799'Type__126
                     (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_124) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_initial_336)
                       else coe seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-once
d_optimize'45'once_4144 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'once_4144 v0 v1 v2
  = let v3
          = d__'8799'Type__126
              (coe v1) (coe MAlonzo.Code.Once.Type.C_Unit_122) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (let v6
                              = d_has'45'effect'63'_3756
                                  (coe v0) (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v2) in
                        coe
                          (if coe v6
                             then coe
                                    d_optimize'45'once'45'structural_4138 (coe v0)
                                    (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v2)
                             else coe MAlonzo.Code.Once.CCC.IR.C_terminal_332))
                else coe
                       seq (coe v5)
                       (let v6
                              = d__'8799'Type__126
                                  (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_124) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe
                                           seq (coe v8) (coe MAlonzo.Code.Once.CCC.IR.C_initial_336)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              d_optimize'45'once'45'structural_4138 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-nt
d_optimize'45'nt_4150 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276
d_optimize'45'nt_4150 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_426 -> coe v2
      MAlonzo.Code.Once.CCC.IR.C_ntK_432 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v7
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_ntK_432
                           (d_optimize'45'once_4144 (coe v6) (coe v7) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntFst_440 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntFst_440
                    (d_optimize'45'nt_4150 (coe v7) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_448 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntSnd_448
                    (d_optimize'45'nt_4150 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntCase_456 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntCase_456
                    (d_optimize'45'nt_4150 (coe v8) (coe v1) (coe v6))
                    (d_optimize'45'nt_4150 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInl_464 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntInl_464
                    (d_optimize'45'nt_4150 (coe v0) (coe v7) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInr_472 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntInr_472
                    (d_optimize'45'nt_4150 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntPair_480 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntPair_480
                    (d_optimize'45'nt_4150 (coe v0) (coe v8) (coe v6))
                    (d_optimize'45'nt_4150 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-n
d_optimize'45'n_4368 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize'45'n_4368 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_4368 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_4144 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_4380 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_optimize_4380 v0 v1
  = coe d_optimize'45'n_4368 (coe v0) (coe v1) (coe (10 :: Integer))
