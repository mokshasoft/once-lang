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
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Optimize._≟Type_
d__'8799'Type__8 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Type__8 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Void_8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v4 v5
               -> let v6 = d__'8799'Type__8 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'Type__8 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             MAlonzo.Code.Once.Type.C__'43'__12 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v4 v5
               -> let v6 = d__'8799'Type__8 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'Type__8 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             MAlonzo.Code.Once.Type.C__'8658'__14 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v4 v5
               -> let v6 = d__'8799'Type__8 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'Type__8 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             MAlonzo.Code.Once.Type.C_Eff_16 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v4 v5
               -> let v6 = d__'8799'Type__8 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'Type__8 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             MAlonzo.Code.Once.Type.C_Fix_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Fix_18 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v3
               -> let v4 = d__'8799'Type__8 (coe v2) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_20
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Str_22
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Buffer_24
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_TVar_26 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_TVar_26 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_26 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v2))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v2)
                               (coe v3)) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟IR_
d__'8799'IR__434 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IR__434 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_8
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_id_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C__'8728'__16 v6 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_72 v8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C__'8728'__16 v5 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_id_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C__'8728'__16 v10 v12 v13
               -> let v14 = d__'8799'Type__8 (coe v5) (coe v10) in
                  coe
                    (case coe v14 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                         -> if coe v15
                              then case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                       -> let v18
                                                = d__'8799'IR__434
                                                    (coe v5) (coe v1) (coe v7) (coe v12) in
                                          coe
                                            (let v19
                                                   = d__'8799'IR__434
                                                       (coe v0) (coe v5) (coe v8) (coe v13) in
                                             coe
                                               (let v20
                                                      = case coe v19 of
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                            -> coe
                                                                 seq (coe v20)
                                                                 (coe
                                                                    seq (coe v21)
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                                          _ -> MAlonzo.RTE.mazUnreachableError in
                                                coe
                                                  (case coe v18 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                       -> let v23
                                                                = case coe v19 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                      -> case coe v23 of
                                                                           MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                                             -> case coe v24 of
                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                    -> coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                         (coe v23)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                                  _ -> coe v20
                                                                           _ -> coe v20
                                                                    _ -> MAlonzo.RTE.mazUnreachableError in
                                                          coe
                                                            (if coe v21
                                                               then case coe v22 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v24
                                                                        -> case coe v19 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                               -> case coe v25 of
                                                                                    MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                      -> case coe
                                                                                                v26 of
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v27
                                                                                             -> coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                  (coe
                                                                                                     v25)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                     erased)
                                                                                           _ -> coe
                                                                                                  v23
                                                                                    _ -> coe v23
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v23
                                                               else (case coe v22 of
                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                         -> coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                              (coe v21)
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                       _ -> coe v23))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v16)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v15)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.IR.C_fst_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_snd_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inl_42
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inr_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v12 v13
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_72 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_apply_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fold_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_unfold_86
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_arr_92
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fst_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_snd_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_72 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_28
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fst_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_snd_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_72 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_apply_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__10 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_id_8
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C__'8728'__16 v12 v14 v15
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_fst_22
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_snd_28
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
                      -> let v16
                               = d__'8799'IR__434 (coe v0) (coe v9) (coe v7) (coe v14) in
                         coe
                           (let v17
                                  = d__'8799'IR__434 (coe v0) (coe v10) (coe v8) (coe v15) in
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
                    MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v14 v15
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_initial_64
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_apply_78
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_unfold_86
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_42
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inl_42
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_inr_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_48
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inl_42
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inr_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__12 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_id_8
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C__'8728'__16 v12 v14 v15
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_inl_42
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_inr_48
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v14 v15
                      -> let v16
                               = d__'8799'IR__434 (coe v9) (coe v1) (coe v7) (coe v14) in
                         coe
                           (let v17
                                  = d__'8799'IR__434 (coe v10) (coe v1) (coe v8) (coe v15) in
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
                    MAlonzo.Code.Once.IR.C_terminal_60
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_curry_72 v14
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_fold_82
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_60
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_id_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C__'8728'__16 v6 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fst_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_snd_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_initial_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_apply_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_unfold_86
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_initial_64
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_id_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C__'8728'__16 v6 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inl_42
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inr_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_curry_72 v8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fold_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_curry_72 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_id_8
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C__'8728'__16 v11 v13 v14
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_fst_22
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_snd_28
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v13 v14
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_initial_64
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_curry_72 v13
                      -> let v14
                               = d__'8799'IR__434
                                   (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v8))
                                   (coe v9) (coe v7) (coe v13) in
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
                    MAlonzo.Code.Once.IR.C_apply_78
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_unfold_86
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_78
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_snd_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_72 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_apply_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fold_82
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__16 v6 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fold_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_unfold_86
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__16 v6 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_72 v8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_unfold_86
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_arr_92
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_arr_92
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-compose
d_optimize'45'compose_666 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'compose_666 v0 v1 v2 v3 v4
  = let v5 = coe MAlonzo.Code.Once.IR.C__'8728'__16 v1 v3 v4 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C_id_8 -> coe v4
         MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
           -> let v11
                    = d_optimize'45'compose_666
                        (coe v0) (coe v7) (coe v2) (coe v9)
                        (coe
                           d_optimize'45'compose_666 (coe v0) (coe v1) (coe v7) (coe v10)
                           (coe v4)) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Once.IR.C_id_8
                     -> coe MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
                   MAlonzo.Code.Once.IR.C_initial_64
                     -> coe MAlonzo.Code.Once.IR.C_initial_64
                   _ -> coe v11)
         MAlonzo.Code.Once.IR.C_fst_22
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_8 -> coe MAlonzo.Code.Once.IR.C_fst_22
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v13 v14 -> coe v13
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v13 v14
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                     (d_optimize'45'compose_666
                                        (coe v15)
                                        (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v2) (coe v9))
                                        (coe v2) (coe MAlonzo.Code.Once.IR.C_fst_22) (coe v13))
                                     (d_optimize'45'compose_666
                                        (coe v16)
                                        (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v2) (coe v9))
                                        (coe v2) (coe MAlonzo.Code.Once.IR.C_fst_22) (coe v14))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_64
                         -> coe MAlonzo.Code.Once.IR.C_initial_64
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_snd_28
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_8 -> coe MAlonzo.Code.Once.IR.C_snd_28
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v13 v14 -> coe v14
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v13 v14
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                     (d_optimize'45'compose_666
                                        (coe v15)
                                        (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v8) (coe v2))
                                        (coe v2) (coe MAlonzo.Code.Once.IR.C_snd_28) (coe v13))
                                     (d_optimize'45'compose_666
                                        (coe v16)
                                        (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v8) (coe v2))
                                        (coe v2) (coe MAlonzo.Code.Once.IR.C_snd_28) (coe v14))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_64
                         -> coe MAlonzo.Code.Once.IR.C_initial_64
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__10 v11 v12
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_8
                         -> coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
                       MAlonzo.Code.Once.IR.C__'8728'__16 v14 v16 v17
                         -> coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                              (d_optimize'45'compose_666
                                 (coe v0) (coe v1) (coe v11) (coe v9)
                                 (coe MAlonzo.Code.Once.IR.C__'8728'__16 v14 v16 v17))
                              (d_optimize'45'compose_666
                                 (coe v0) (coe v1) (coe v12) (coe v10)
                                 (coe MAlonzo.Code.Once.IR.C__'8728'__16 v14 v16 v17))
                       MAlonzo.Code.Once.IR.C_fst_22
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'42'__10 v15 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (d_optimize'45'compose_666
                                        (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v1) (coe v16))
                                        (coe v1) (coe v11) (coe v9)
                                        (coe MAlonzo.Code.Once.IR.C_fst_22))
                                     (d_optimize'45'compose_666
                                        (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v1) (coe v16))
                                        (coe v1) (coe v12) (coe v10)
                                        (coe MAlonzo.Code.Once.IR.C_fst_22))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_snd_28
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'42'__10 v15 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (d_optimize'45'compose_666
                                        (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v15) (coe v1))
                                        (coe v1) (coe v11) (coe v9)
                                        (coe MAlonzo.Code.Once.IR.C_snd_28))
                                     (d_optimize'45'compose_666
                                        (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v15) (coe v1))
                                        (coe v1) (coe v12) (coe v10)
                                        (coe MAlonzo.Code.Once.IR.C_snd_28))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v16 v17
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'42'__10 v18 v19
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (d_optimize'45'compose_666
                                        (coe v0) (coe v1) (coe v11) (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v16 v17))
                                     (d_optimize'45'compose_666
                                        (coe v0) (coe v1) (coe v12) (coe v10)
                                        (coe
                                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v16 v17))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_inl_42
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (d_optimize'45'compose_666
                                        (coe v0)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v0) (coe v16))
                                        (coe v11) (coe v9) (coe MAlonzo.Code.Once.IR.C_inl_42))
                                     (d_optimize'45'compose_666
                                        (coe v0)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v0) (coe v16))
                                        (coe v12) (coe v10) (coe MAlonzo.Code.Once.IR.C_inl_42))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_inr_48
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (d_optimize'45'compose_666
                                        (coe v0)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v15) (coe v0))
                                        (coe v11) (coe v9) (coe MAlonzo.Code.Once.IR.C_inr_48))
                                     (d_optimize'45'compose_666
                                        (coe v0)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v15) (coe v0))
                                        (coe v12) (coe v10) (coe MAlonzo.Code.Once.IR.C_inr_48))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v16 v17
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__12 v18 v19
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (d_optimize'45'compose_666
                                        (coe v0) (coe v1) (coe v11) (coe v9)
                                        (coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v16 v17))
                                     (d_optimize'45'compose_666
                                        (coe v0) (coe v1) (coe v12) (coe v10)
                                        (coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v16 v17))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_terminal_60
                         -> coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                              (d_optimize'45'compose_666
                                 (coe v0) (coe MAlonzo.Code.Once.Type.C_Unit_6) (coe v11) (coe v9)
                                 (coe MAlonzo.Code.Once.IR.C_terminal_60))
                              (d_optimize'45'compose_666
                                 (coe v0) (coe MAlonzo.Code.Once.Type.C_Unit_6) (coe v12) (coe v10)
                                 (coe MAlonzo.Code.Once.IR.C_terminal_60))
                       MAlonzo.Code.Once.IR.C_initial_64
                         -> coe MAlonzo.Code.Once.IR.C_initial_64
                       MAlonzo.Code.Once.IR.C_curry_72 v16
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'8658'__14 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (d_optimize'45'compose_666
                                        (coe v0) (coe v1) (coe v11) (coe v9)
                                        (coe MAlonzo.Code.Once.IR.C_curry_72 v16))
                                     (d_optimize'45'compose_666
                                        (coe v0) (coe v1) (coe v12) (coe v10)
                                        (coe MAlonzo.Code.Once.IR.C_curry_72 v16))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_apply_78
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'42'__10 v15 v16
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Type.C__'8658'__14 v17 v18
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                            (d_optimize'45'compose_666
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__10
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658'__14 (coe v17)
                                                     (coe v1))
                                                  (coe v17))
                                               (coe v1) (coe v11) (coe v9)
                                               (coe MAlonzo.Code.Once.IR.C_apply_78))
                                            (d_optimize'45'compose_666
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__10
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658'__14 (coe v17)
                                                     (coe v1))
                                                  (coe v17))
                                               (coe v1) (coe v12) (coe v10)
                                               (coe MAlonzo.Code.Once.IR.C_apply_78))
                                     _ -> coe v5
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_fold_82
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C_Fix_18 v14
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (d_optimize'45'compose_666
                                        (coe v0) (coe MAlonzo.Code.Once.Type.C_Fix_18 (coe v0))
                                        (coe v11) (coe v9) (coe MAlonzo.Code.Once.IR.C_fold_82))
                                     (d_optimize'45'compose_666
                                        (coe v0) (coe MAlonzo.Code.Once.Type.C_Fix_18 (coe v0))
                                        (coe v12) (coe v10) (coe MAlonzo.Code.Once.IR.C_fold_82))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_unfold_86
                         -> coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                              (d_optimize'45'compose_666
                                 (coe MAlonzo.Code.Once.Type.C_Fix_18 (coe v1)) (coe v1) (coe v11)
                                 (coe v9) (coe MAlonzo.Code.Once.IR.C_unfold_86))
                              (d_optimize'45'compose_666
                                 (coe MAlonzo.Code.Once.Type.C_Fix_18 (coe v1)) (coe v1) (coe v12)
                                 (coe v10) (coe MAlonzo.Code.Once.IR.C_unfold_86))
                       MAlonzo.Code.Once.IR.C_arr_92
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'8658'__14 v15 v16
                                -> case coe v1 of
                                     MAlonzo.Code.Once.Type.C_Eff_16 v17 v18
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                            (d_optimize'45'compose_666
                                               (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_Eff_16 (coe v15)
                                                  (coe v16))
                                               (coe v11) (coe v9)
                                               (coe MAlonzo.Code.Once.IR.C_arr_92))
                                            (d_optimize'45'compose_666
                                               (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_Eff_16 (coe v15)
                                                  (coe v16))
                                               (coe v12) (coe v10)
                                               (coe MAlonzo.Code.Once.IR.C_arr_92))
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inl_42
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_8 -> coe MAlonzo.Code.Once.IR.C_inl_42
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v13 v14
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                     (d_optimize'45'compose_666
                                        (coe v15) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v1) (coe v9))
                                        (coe MAlonzo.Code.Once.IR.C_inl_42) (coe v13))
                                     (d_optimize'45'compose_666
                                        (coe v16) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v1) (coe v9))
                                        (coe MAlonzo.Code.Once.IR.C_inl_42) (coe v14))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_64
                         -> coe MAlonzo.Code.Once.IR.C_initial_64
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inr_48
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_8 -> coe MAlonzo.Code.Once.IR.C_inr_48
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v13 v14
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                     (d_optimize'45'compose_666
                                        (coe v15) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v8) (coe v1))
                                        (coe MAlonzo.Code.Once.IR.C_inr_48) (coe v13))
                                     (d_optimize'45'compose_666
                                        (coe v16) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v8) (coe v1))
                                        (coe MAlonzo.Code.Once.IR.C_inr_48) (coe v14))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_64
                         -> coe MAlonzo.Code.Once.IR.C_initial_64
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__12 v11 v12
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_8
                         -> coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v9 v10
                       MAlonzo.Code.Once.IR.C_inl_42 -> coe v9
                       MAlonzo.Code.Once.IR.C_inr_48 -> coe v10
                       MAlonzo.Code.Once.IR.C_initial_64
                         -> coe MAlonzo.Code.Once.IR.C_initial_64
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_terminal_60
           -> case coe v4 of
                MAlonzo.Code.Once.IR.C_id_8
                  -> coe MAlonzo.Code.Once.IR.C_terminal_60
                MAlonzo.Code.Once.IR.C__'8728'__16 v8 v10 v11
                  -> coe MAlonzo.Code.Once.IR.C_terminal_60
                MAlonzo.Code.Once.IR.C_fst_22
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'42'__10 v9 v10
                         -> coe MAlonzo.Code.Once.IR.C_terminal_60
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_snd_28
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'42'__10 v9 v10
                         -> coe MAlonzo.Code.Once.IR.C_terminal_60
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v10 v11
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'42'__10 v12 v13
                         -> coe MAlonzo.Code.Once.IR.C_terminal_60
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_inl_42
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'43'__12 v9 v10
                         -> coe MAlonzo.Code.Once.IR.C_terminal_60
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_inr_48
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'43'__12 v9 v10
                         -> coe MAlonzo.Code.Once.IR.C_terminal_60
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v10 v11
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'43'__12 v12 v13
                         -> coe MAlonzo.Code.Once.IR.C_terminal_60
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_terminal_60
                  -> coe MAlonzo.Code.Once.IR.C_terminal_60
                MAlonzo.Code.Once.IR.C_initial_64
                  -> coe MAlonzo.Code.Once.IR.C_initial_64
                MAlonzo.Code.Once.IR.C_curry_72 v10
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658'__14 v11 v12
                         -> coe MAlonzo.Code.Once.IR.C_terminal_60
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_apply_78
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'42'__10 v9 v10
                         -> case coe v9 of
                              MAlonzo.Code.Once.Type.C__'8658'__14 v11 v12
                                -> coe MAlonzo.Code.Once.IR.C_terminal_60
                              _ -> coe v5
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_fold_82
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C_Fix_18 v8
                         -> coe MAlonzo.Code.Once.IR.C_terminal_60
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_unfold_86
                  -> coe MAlonzo.Code.Once.IR.C_terminal_60
                MAlonzo.Code.Once.IR.C_arr_92
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'8658'__14 v9 v10
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C_Eff_16 v11 v12
                                -> coe MAlonzo.Code.Once.IR.C_terminal_60
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.IR.C_curry_72 v9
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'8658'__14 v10 v11
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_8
                         -> coe MAlonzo.Code.Once.IR.C_curry_72 v9
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v15 v16
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__12 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                     (d_optimize'45'compose_666
                                        (coe v17) (coe v1) (coe v2)
                                        (coe MAlonzo.Code.Once.IR.C_curry_72 v9) (coe v15))
                                     (d_optimize'45'compose_666
                                        (coe v18) (coe v1) (coe v2)
                                        (coe MAlonzo.Code.Once.IR.C_curry_72 v9) (coe v16))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_64
                         -> coe MAlonzo.Code.Once.IR.C_initial_64
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_apply_78
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
                  -> case coe v8 of
                       MAlonzo.Code.Once.Type.C__'8658'__14 v10 v11
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C_id_8 -> coe MAlonzo.Code.Once.IR.C_apply_78
                              MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v15 v16
                                -> case coe v0 of
                                     MAlonzo.Code.Once.Type.C__'43'__12 v17 v18
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                            (d_optimize'45'compose_666
                                               (coe v17)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__10
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658'__14 (coe v10)
                                                     (coe v2))
                                                  (coe v10))
                                               (coe v2) (coe MAlonzo.Code.Once.IR.C_apply_78)
                                               (coe v15))
                                            (d_optimize'45'compose_666
                                               (coe v18)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__10
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658'__14 (coe v10)
                                                     (coe v2))
                                                  (coe v10))
                                               (coe v2) (coe MAlonzo.Code.Once.IR.C_apply_78)
                                               (coe v16))
                                     _ -> coe v5
                              MAlonzo.Code.Once.IR.C_initial_64
                                -> coe MAlonzo.Code.Once.IR.C_initial_64
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_fold_82
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_Fix_18 v7
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_8 -> coe MAlonzo.Code.Once.IR.C_fold_82
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v11 v12
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__12 v13 v14
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                     (d_optimize'45'compose_666
                                        (coe v13) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C_Fix_18 (coe v1))
                                        (coe MAlonzo.Code.Once.IR.C_fold_82) (coe v11))
                                     (d_optimize'45'compose_666
                                        (coe v14) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C_Fix_18 (coe v1))
                                        (coe MAlonzo.Code.Once.IR.C_fold_82) (coe v12))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_64
                         -> coe MAlonzo.Code.Once.IR.C_initial_64
                       MAlonzo.Code.Once.IR.C_unfold_86 -> coe MAlonzo.Code.Once.IR.C_id_8
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_unfold_86
           -> case coe v4 of
                MAlonzo.Code.Once.IR.C_id_8 -> coe MAlonzo.Code.Once.IR.C_unfold_86
                MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v10 v11
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'43'__12 v12 v13
                         -> coe
                              MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                              (d_optimize'45'compose_666
                                 (coe v12) (coe MAlonzo.Code.Once.Type.C_Fix_18 (coe v2)) (coe v2)
                                 (coe MAlonzo.Code.Once.IR.C_unfold_86) (coe v10))
                              (d_optimize'45'compose_666
                                 (coe v13) (coe MAlonzo.Code.Once.Type.C_Fix_18 (coe v2)) (coe v2)
                                 (coe MAlonzo.Code.Once.IR.C_unfold_86) (coe v11))
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_initial_64
                  -> coe MAlonzo.Code.Once.IR.C_initial_64
                MAlonzo.Code.Once.IR.C_fold_82 -> coe MAlonzo.Code.Once.IR.C_id_8
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_arr_92
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658'__14 v8 v9
                  -> case coe v2 of
                       MAlonzo.Code.Once.Type.C_Eff_16 v10 v11
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C_id_8 -> coe MAlonzo.Code.Once.IR.C_arr_92
                              MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v15 v16
                                -> case coe v0 of
                                     MAlonzo.Code.Once.Type.C__'43'__12 v17 v18
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                            (d_optimize'45'compose_666
                                               (coe v17) (coe v1)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_Eff_16 (coe v8) (coe v9))
                                               (coe MAlonzo.Code.Once.IR.C_arr_92) (coe v15))
                                            (d_optimize'45'compose_666
                                               (coe v18) (coe v1)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_Eff_16 (coe v8) (coe v9))
                                               (coe MAlonzo.Code.Once.IR.C_arr_92) (coe v16))
                                     _ -> coe v5
                              MAlonzo.Code.Once.IR.C_initial_64
                                -> coe MAlonzo.Code.Once.IR.C_initial_64
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         _ -> coe v5)
-- Once.Optimize.optimize-pair
d_optimize'45'pair_848 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'pair_848 v0 v1 v2 v3 v4
  = let v5
          = coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v3 v4 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
           -> case coe v9 of
                MAlonzo.Code.Once.IR.C_fst_22
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C__'42'__10 v13 v14
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C__'8728'__16 v16 v18 v19
                                -> case coe v18 of
                                     MAlonzo.Code.Once.IR.C_snd_28
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C__'42'__10 v22 v23
                                              -> let v24 = d__'8799'Type__8 (coe v0) (coe v22) in
                                                 coe
                                                   (let v25 = d__'8799'Type__8 (coe v14) (coe v1) in
                                                    coe
                                                      (case coe v24 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                           -> let v28
                                                                    = coe
                                                                        MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                                        (coe
                                                                           MAlonzo.Code.Once.IR.C__'8728'__16
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'42'__10
                                                                              (coe v0) (coe v14))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_fst_22)
                                                                           v10)
                                                                        (coe
                                                                           MAlonzo.Code.Once.IR.C__'8728'__16
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'42'__10
                                                                              (coe v22) (coe v1))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_snd_28)
                                                                           v19) in
                                                              coe
                                                                (case coe v26 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v27 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v29
                                                                            -> case coe v25 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                   -> case coe
                                                                                             v30 of
                                                                                        MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                          -> case coe
                                                                                                    v31 of
                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v32
                                                                                                 -> let v33
                                                                                                          = d__'8799'IR__434
                                                                                                              (coe
                                                                                                                 v2)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.Type.C__'42'__10
                                                                                                                 (coe
                                                                                                                    v0)
                                                                                                                 (coe
                                                                                                                    v1))
                                                                                                              (coe
                                                                                                                 v10)
                                                                                                              (coe
                                                                                                                 v19) in
                                                                                                    coe
                                                                                                      (case coe
                                                                                                              v33 of
                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                           -> if coe
                                                                                                                   v34
                                                                                                                then coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v35)
                                                                                                                       (coe
                                                                                                                          v10)
                                                                                                                else coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v35)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.IR.C__'8728'__16
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Type.C__'42'__10
                                                                                                                                (coe
                                                                                                                                   v0)
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.IR.C_fst_22)
                                                                                                                             v10)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.IR.C__'8728'__16
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Type.C__'42'__10
                                                                                                                                (coe
                                                                                                                                   v0)
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.IR.C_snd_28)
                                                                                                                             v19))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                               _ -> coe
                                                                                                      v28
                                                                                        _ -> coe v28
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> coe v28
                                                                   _ -> coe v28)
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_fst_22
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_snd_28
                         -> let v12 = d__'8799'Type__8 (coe v0) (coe v0) in
                            coe
                              (let v13 = d__'8799'Type__8 (coe v1) (coe v1) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                      -> let v16
                                               = coe
                                                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                   (coe MAlonzo.Code.Once.IR.C_fst_22)
                                                   (coe MAlonzo.Code.Once.IR.C_snd_28) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                -> case coe v15 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                              -> case coe v18 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v19 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                                            -> coe
                                                                                 MAlonzo.Code.Once.IR.C_id_8
                                                                          _ -> coe v16
                                                                   _ -> coe v16
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v16
                                              _ -> coe v16)
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> coe v5
                _ -> coe v5
         _ -> coe v5)
-- Once.Optimize.optimize-case
d_optimize'45'case_972 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'case_972 v0 v1 v2 v3 v4
  = let v5 = coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v3 v4 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C__'8728'__16 v7 v9 v10
           -> case coe v10 of
                MAlonzo.Code.Once.IR.C_inl_42
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C__'43'__12 v13 v14
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C__'8728'__16 v16 v18 v19
                                -> case coe v19 of
                                     MAlonzo.Code.Once.IR.C_inr_48
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C__'43'__12 v22 v23
                                              -> let v24 = d__'8799'Type__8 (coe v0) (coe v22) in
                                                 coe
                                                   (let v25 = d__'8799'Type__8 (coe v14) (coe v1) in
                                                    coe
                                                      (case coe v24 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                           -> let v28
                                                                    = coe
                                                                        MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                                                        (coe
                                                                           MAlonzo.Code.Once.IR.C__'8728'__16
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'43'__12
                                                                              (coe v0) (coe v14))
                                                                           v9
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_inl_42))
                                                                        (coe
                                                                           MAlonzo.Code.Once.IR.C__'8728'__16
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'43'__12
                                                                              (coe v22) (coe v1))
                                                                           v18
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_inr_48)) in
                                                              coe
                                                                (case coe v26 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v27 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v29
                                                                            -> case coe v25 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                   -> case coe
                                                                                             v30 of
                                                                                        MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                          -> case coe
                                                                                                    v31 of
                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v32
                                                                                                 -> let v33
                                                                                                          = d__'8799'IR__434
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.Type.C__'43'__12
                                                                                                                 (coe
                                                                                                                    v0)
                                                                                                                 (coe
                                                                                                                    v1))
                                                                                                              (coe
                                                                                                                 v2)
                                                                                                              (coe
                                                                                                                 v9)
                                                                                                              (coe
                                                                                                                 v18) in
                                                                                                    coe
                                                                                                      (case coe
                                                                                                              v33 of
                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                           -> if coe
                                                                                                                   v34
                                                                                                                then coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v35)
                                                                                                                       (coe
                                                                                                                          v9)
                                                                                                                else coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v35)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.IR.C__'8728'__16
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Type.C__'43'__12
                                                                                                                                (coe
                                                                                                                                   v0)
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                             v9
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.IR.C_inl_42))
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.IR.C__'8728'__16
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Type.C__'43'__12
                                                                                                                                (coe
                                                                                                                                   v0)
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                             v18
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.IR.C_inr_48)))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                               _ -> coe
                                                                                                      v28
                                                                                        _ -> coe v28
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> coe v28
                                                                   _ -> coe v28)
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inl_42
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_inr_48
                         -> let v12 = d__'8799'Type__8 (coe v0) (coe v0) in
                            coe
                              (let v13 = d__'8799'Type__8 (coe v1) (coe v1) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                      -> let v16
                                               = coe
                                                   MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56
                                                   (coe MAlonzo.Code.Once.IR.C_inl_42)
                                                   (coe MAlonzo.Code.Once.IR.C_inr_48) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                -> case coe v15 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                              -> case coe v18 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v19 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                                            -> coe
                                                                                 MAlonzo.Code.Once.IR.C_id_8
                                                                          _ -> coe v16
                                                                   _ -> coe v16
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v16
                                              _ -> coe v16)
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> coe v5
                _ -> coe v5
         _ -> coe v5)
-- Once.Optimize.optimize-once
d_optimize'45'once_1094 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'once_1094 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_8 -> coe MAlonzo.Code.Once.IR.C_id_8
      MAlonzo.Code.Once.IR.C__'8728'__16 v4 v6 v7
        -> coe
             d_optimize'45'compose_666 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_1094 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_1094 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_fst_22 -> coe MAlonzo.Code.Once.IR.C_fst_22
      MAlonzo.Code.Once.IR.C_snd_28 -> coe MAlonzo.Code.Once.IR.C_snd_28
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
               -> coe
                    d_optimize'45'pair_848 (coe v8) (coe v9) (coe v0)
                    (coe d_optimize'45'once_1094 (coe v0) (coe v8) (coe v6))
                    (coe d_optimize'45'once_1094 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_42 -> coe MAlonzo.Code.Once.IR.C_inl_42
      MAlonzo.Code.Once.IR.C_inr_48 -> coe MAlonzo.Code.Once.IR.C_inr_48
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_56 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
               -> coe
                    d_optimize'45'case_972 (coe v8) (coe v9) (coe v1)
                    (coe d_optimize'45'once_1094 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_1094 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_60
        -> coe MAlonzo.Code.Once.IR.C_terminal_60
      MAlonzo.Code.Once.IR.C_initial_64
        -> coe MAlonzo.Code.Once.IR.C_initial_64
      MAlonzo.Code.Once.IR.C_curry_72 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_72
                    (d_optimize'45'once_1094
                       (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v7)) (coe v8)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_78
        -> coe MAlonzo.Code.Once.IR.C_apply_78
      MAlonzo.Code.Once.IR.C_fold_82
        -> coe MAlonzo.Code.Once.IR.C_fold_82
      MAlonzo.Code.Once.IR.C_unfold_86
        -> coe MAlonzo.Code.Once.IR.C_unfold_86
      MAlonzo.Code.Once.IR.C_arr_92 -> coe MAlonzo.Code.Once.IR.C_arr_92
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-n
d_optimize'45'n_1114 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'n_1114 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_1114 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_1094 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_1126 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize_1126 v0 v1
  = coe d_optimize'45'n_1114 (coe v0) (coe v1) (coe (10 :: Integer))
