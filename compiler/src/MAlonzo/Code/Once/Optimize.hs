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
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Type__8 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_34
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Void_36
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v4 v5
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
             MAlonzo.Code.Once.Type.C__'43'__40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v4 v5
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
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v5 v6 v7
               -> let v8 = d__'8799'Type__8 (coe v2) (coe v5) in
                  coe
                    (let v9
                           = MAlonzo.Code.Once.Type.d__'8799'q__26 (coe v3) (coe v6) in
                     coe
                       (let v10 = d__'8799'Type__8 (coe v4) (coe v7) in
                        coe
                          (let v11
                                 = let v11
                                         = case coe v10 of
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                               -> coe
                                                    seq (coe v11)
                                                    (coe
                                                       seq (coe v12)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                             _ -> MAlonzo.RTE.mazUnreachableError in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> case coe v12 of
                                               MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                 -> case coe v13 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                        -> coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v12)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                      _ -> coe v11
                                               _ -> coe v11
                                        _ -> MAlonzo.RTE.mazUnreachableError) in
                           coe
                             (case coe v8 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                  -> let v14
                                           = let v14
                                                   = case coe v10 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                         -> case coe v14 of
                                                              MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                                -> case coe v15 of
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                       -> coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe v14)
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                     _ -> coe v11
                                                              _ -> coe v11
                                                       _ -> MAlonzo.RTE.mazUnreachableError in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                    -> case coe v15 of
                                                         MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                           -> case coe v16 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                  -> coe
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                       (coe v15)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                _ -> coe v14
                                                         _ -> coe v14
                                                  _ -> MAlonzo.RTE.mazUnreachableError) in
                                     coe
                                       (if coe v12
                                          then case coe v13 of
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                   -> case coe v9 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                          -> case coe v16 of
                                                               MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                 -> case coe v17 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                                        -> case coe v10 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                               -> case coe v19 of
                                                                                    MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                      -> case coe
                                                                                                v20 of
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v21
                                                                                             -> coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                     erased)
                                                                                           _ -> coe
                                                                                                  v14
                                                                                    _ -> coe v14
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v14
                                                               _ -> coe v14
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 _ -> coe v14
                                          else (case coe v13 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                    -> coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                  _ -> coe v14))
                                _ -> MAlonzo.RTE.mazUnreachableError))))
             MAlonzo.Code.Once.Type.C_Eff_44 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v4 v5
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
             MAlonzo.Code.Once.Type.C_Fix_46 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Fix_46 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v3
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
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_48
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Float_50
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Str_52
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Buffer_54
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_TVar_56 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v3
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
d__'8799'IR__508 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IR__508 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_10
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_id_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C__'8728'__20 v8 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_84
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_94 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C__'8728'__20 v6 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_id_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C__'8728'__20 v12 v14 v15
               -> let v16 = d__'8799'Type__8 (coe v6) (coe v12) in
                  coe
                    (case coe v16 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                         -> if coe v17
                              then case coe v18 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                       -> let v20
                                                = d__'8799'IR__508
                                                    (coe v6) (coe v1) (coe v8) (coe v14) in
                                          coe
                                            (let v21
                                                   = d__'8799'IR__508
                                                       (coe v0) (coe v6) (coe v9) (coe v15) in
                                             coe
                                               (let v22
                                                      = case coe v21 of
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                            -> coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    seq (coe v23)
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                                          _ -> MAlonzo.RTE.mazUnreachableError in
                                                coe
                                                  (case coe v20 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                       -> let v25
                                                                = case coe v21 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                      -> case coe v25 of
                                                                           MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                                             -> case coe v26 of
                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                    -> coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                         (coe v25)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                                  _ -> coe v22
                                                                           _ -> coe v22
                                                                    _ -> MAlonzo.RTE.mazUnreachableError in
                                                          coe
                                                            (if coe v23
                                                               then case coe v24 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v26
                                                                        -> case coe v21 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                               -> case coe v27 of
                                                                                    MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                      -> case coe
                                                                                                v28 of
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v29
                                                                                             -> coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                  (coe
                                                                                                     v27)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                     erased)
                                                                                           _ -> coe
                                                                                                  v25
                                                                                    _ -> coe v25
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v25
                                                               else (case coe v24 of
                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                         -> coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                              (coe v23)
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                       _ -> coe v25))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v18)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v17)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.IR.C_fst_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_snd_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v14 v15
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inl_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inr_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v14 v15
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_84
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_94 v14
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_apply_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fold_108
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_unfold_114
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_arr_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_28
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__20 v9 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fst_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_snd_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_94 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_36
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__20 v9 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fst_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_snd_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_94 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_apply_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_id_10
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C__'8728'__20 v14 v16 v17
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_fst_28
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_snd_36
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v16 v17
                      -> let v18
                               = d__'8799'IR__508 (coe v0) (coe v10) (coe v8) (coe v16) in
                         coe
                           (let v19
                                  = d__'8799'IR__508 (coe v0) (coe v11) (coe v9) (coe v17) in
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
                                                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
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
                                                                     -> case coe v26 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v27
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v25)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                    erased)
                                                                          _ -> coe v23
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
                    MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v16 v17
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_initial_84
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_apply_102
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_unfold_114
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_54
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__20 v9 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inl_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_inr_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_84
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_62
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__20 v9 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inl_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inr_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_84
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_id_10
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C__'8728'__20 v14 v16 v17
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v16 v17
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_inl_54
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_inr_62
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v16 v17
                      -> let v18
                               = d__'8799'IR__508 (coe v10) (coe v1) (coe v8) (coe v16) in
                         coe
                           (let v19
                                  = d__'8799'IR__508 (coe v11) (coe v1) (coe v9) (coe v17) in
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
                                                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
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
                                                                     -> case coe v26 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v27
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v25)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                    erased)
                                                                          _ -> coe v23
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
                    MAlonzo.Code.Once.IR.C_terminal_78
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_curry_94 v16
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_fold_108
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_78
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_id_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C__'8728'__20 v8 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fst_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_snd_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_initial_84
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_apply_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_unfold_114
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_initial_84
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_id_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C__'8728'__20 v8 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inl_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_inr_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_84
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.IR.C_curry_94 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fold_108
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_curry_94 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_id_10
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C__'8728'__20 v14 v16 v17
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_fst_28
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_snd_36
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v16 v17
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_initial_84
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_curry_94 v16
                      -> let v17
                               = d__'8799'IR__508
                                   (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                                   (coe v11) (coe v8) (coe v16) in
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
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.IR.C_apply_102
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    MAlonzo.Code.Once.IR.C_unfold_114
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_102
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__20 v9 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_snd_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_94 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_apply_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fold_108
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__20 v8 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_initial_84
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_fold_108
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_unfold_114
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__20 v8 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v10 v11
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_terminal_78
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_curry_94 v10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_unfold_114
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_arr_122
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__20 v9 v11 v12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.IR.C_arr_122
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-compose
d_optimize'45'compose_740 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'compose_740 v0 v1 v2 v3 v4
  = let v5 = coe MAlonzo.Code.Once.IR.C__'8728'__20 v1 v3 v4 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C_id_10 -> coe v4
         MAlonzo.Code.Once.IR.C__'8728'__20 v8 v10 v11
           -> let v12
                    = d_optimize'45'compose_740
                        (coe v0) (coe v8) (coe v2) (coe v10)
                        (coe
                           d_optimize'45'compose_740 (coe v0) (coe v1) (coe v8) (coe v11)
                           (coe v4)) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Once.IR.C_id_10
                     -> coe MAlonzo.Code.Once.IR.C__'8728'__20 v8 v10 v11
                   MAlonzo.Code.Once.IR.C_initial_84
                     -> coe MAlonzo.Code.Once.IR.C_initial_84
                   _ -> coe v12)
         MAlonzo.Code.Once.IR.C_fst_28
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_10 -> coe MAlonzo.Code.Once.IR.C_fst_28
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v15 v16 -> coe v15
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v15 v16
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                     (d_optimize'45'compose_740
                                        (coe v17)
                                        (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v2) (coe v10))
                                        (coe v2) (coe MAlonzo.Code.Once.IR.C_fst_28) (coe v15))
                                     (d_optimize'45'compose_740
                                        (coe v18)
                                        (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v2) (coe v10))
                                        (coe v2) (coe MAlonzo.Code.Once.IR.C_fst_28) (coe v16))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_84
                         -> coe MAlonzo.Code.Once.IR.C_initial_84
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_snd_36
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_10 -> coe MAlonzo.Code.Once.IR.C_snd_36
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v15 v16 -> coe v16
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v15 v16
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                     (d_optimize'45'compose_740
                                        (coe v17)
                                        (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v9) (coe v2))
                                        (coe v2) (coe MAlonzo.Code.Once.IR.C_snd_36) (coe v15))
                                     (d_optimize'45'compose_740
                                        (coe v18)
                                        (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v9) (coe v2))
                                        (coe v2) (coe MAlonzo.Code.Once.IR.C_snd_36) (coe v16))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_84
                         -> coe MAlonzo.Code.Once.IR.C_initial_84
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__38 v12 v13
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_10
                         -> coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v10 v11
                       MAlonzo.Code.Once.IR.C__'8728'__20 v16 v18 v19
                         -> coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                              (d_optimize'45'compose_740
                                 (coe v0) (coe v1) (coe v12) (coe v10)
                                 (coe MAlonzo.Code.Once.IR.C__'8728'__20 v16 v18 v19))
                              (d_optimize'45'compose_740
                                 (coe v0) (coe v1) (coe v13) (coe v11)
                                 (coe MAlonzo.Code.Once.IR.C__'8728'__20 v16 v18 v19))
                       MAlonzo.Code.Once.IR.C_fst_28
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'42'__38 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                     (d_optimize'45'compose_740
                                        (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v1) (coe v18))
                                        (coe v1) (coe v12) (coe v10)
                                        (coe MAlonzo.Code.Once.IR.C_fst_28))
                                     (d_optimize'45'compose_740
                                        (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v1) (coe v18))
                                        (coe v1) (coe v13) (coe v11)
                                        (coe MAlonzo.Code.Once.IR.C_fst_28))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_snd_36
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'42'__38 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                     (d_optimize'45'compose_740
                                        (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v17) (coe v1))
                                        (coe v1) (coe v12) (coe v10)
                                        (coe MAlonzo.Code.Once.IR.C_snd_36))
                                     (d_optimize'45'compose_740
                                        (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v17) (coe v1))
                                        (coe v1) (coe v13) (coe v11)
                                        (coe MAlonzo.Code.Once.IR.C_snd_36))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v18 v19
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'42'__38 v20 v21
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                     (d_optimize'45'compose_740
                                        (coe v0) (coe v1) (coe v12) (coe v10)
                                        (coe
                                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v18 v19))
                                     (d_optimize'45'compose_740
                                        (coe v0) (coe v1) (coe v13) (coe v11)
                                        (coe
                                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v18 v19))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_inl_54
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                     (d_optimize'45'compose_740
                                        (coe v0)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v0) (coe v18))
                                        (coe v12) (coe v10) (coe MAlonzo.Code.Once.IR.C_inl_54))
                                     (d_optimize'45'compose_740
                                        (coe v0)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v0) (coe v18))
                                        (coe v13) (coe v11) (coe MAlonzo.Code.Once.IR.C_inl_54))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_inr_62
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                     (d_optimize'45'compose_740
                                        (coe v0)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v17) (coe v0))
                                        (coe v12) (coe v10) (coe MAlonzo.Code.Once.IR.C_inr_62))
                                     (d_optimize'45'compose_740
                                        (coe v0)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v17) (coe v0))
                                        (coe v13) (coe v11) (coe MAlonzo.Code.Once.IR.C_inr_62))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v18 v19
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v20 v21
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                     (d_optimize'45'compose_740
                                        (coe v0) (coe v1) (coe v12) (coe v10)
                                        (coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v18 v19))
                                     (d_optimize'45'compose_740
                                        (coe v0) (coe v1) (coe v13) (coe v11)
                                        (coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v18 v19))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_terminal_78
                         -> coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                              (d_optimize'45'compose_740
                                 (coe v0) (coe MAlonzo.Code.Once.Type.C_Unit_34) (coe v12) (coe v10)
                                 (coe MAlonzo.Code.Once.IR.C_terminal_78))
                              (d_optimize'45'compose_740
                                 (coe v0) (coe MAlonzo.Code.Once.Type.C_Unit_34) (coe v13) (coe v11)
                                 (coe MAlonzo.Code.Once.IR.C_terminal_78))
                       MAlonzo.Code.Once.IR.C_initial_84
                         -> coe MAlonzo.Code.Once.IR.C_initial_84
                       MAlonzo.Code.Once.IR.C_curry_94 v18
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v19 v20 v21
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                     (d_optimize'45'compose_740
                                        (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 (coe v19)
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                        (coe v12) (coe v10)
                                        (coe MAlonzo.Code.Once.IR.C_curry_94 v18))
                                     (d_optimize'45'compose_740
                                        (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 (coe v19)
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                        (coe v13) (coe v11)
                                        (coe MAlonzo.Code.Once.IR.C_curry_94 v18))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_apply_102
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'42'__38 v17 v18
                                -> case coe v17 of
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v19 v20 v21
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                            (d_optimize'45'compose_740
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__38
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                     (coe v19)
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v1))
                                                  (coe v19))
                                               (coe v1) (coe v12) (coe v10)
                                               (coe MAlonzo.Code.Once.IR.C_apply_102))
                                            (d_optimize'45'compose_740
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__38
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                     (coe v19)
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v1))
                                                  (coe v19))
                                               (coe v1) (coe v13) (coe v11)
                                               (coe MAlonzo.Code.Once.IR.C_apply_102))
                                     _ -> coe v5
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_fold_108
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C_Fix_46 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                     (d_optimize'45'compose_740
                                        (coe v0) (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v0))
                                        (coe v12) (coe v10) (coe MAlonzo.Code.Once.IR.C_fold_108))
                                     (d_optimize'45'compose_740
                                        (coe v0) (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v0))
                                        (coe v13) (coe v11) (coe MAlonzo.Code.Once.IR.C_fold_108))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_unfold_114
                         -> coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                              (d_optimize'45'compose_740
                                 (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v1)) (coe v1) (coe v12)
                                 (coe v10) (coe MAlonzo.Code.Once.IR.C_unfold_114))
                              (d_optimize'45'compose_740
                                 (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v1)) (coe v1) (coe v13)
                                 (coe v11) (coe MAlonzo.Code.Once.IR.C_unfold_114))
                       MAlonzo.Code.Once.IR.C_arr_122
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v17 v18 v19
                                -> case coe v1 of
                                     MAlonzo.Code.Once.Type.C_Eff_44 v20 v21
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                            (d_optimize'45'compose_740
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                  (coe v17) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe v19))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_Eff_44 (coe v17)
                                                  (coe v19))
                                               (coe v12) (coe v10)
                                               (coe MAlonzo.Code.Once.IR.C_arr_122))
                                            (d_optimize'45'compose_740
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                  (coe v17) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe v19))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_Eff_44 (coe v17)
                                                  (coe v19))
                                               (coe v13) (coe v11)
                                               (coe MAlonzo.Code.Once.IR.C_arr_122))
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inl_54
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__40 v9 v10
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_10 -> coe MAlonzo.Code.Once.IR.C_inl_54
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v15 v16
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                     (d_optimize'45'compose_740
                                        (coe v17) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v1) (coe v10))
                                        (coe MAlonzo.Code.Once.IR.C_inl_54) (coe v15))
                                     (d_optimize'45'compose_740
                                        (coe v18) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v1) (coe v10))
                                        (coe MAlonzo.Code.Once.IR.C_inl_54) (coe v16))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_84
                         -> coe MAlonzo.Code.Once.IR.C_initial_84
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inr_62
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__40 v9 v10
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_10 -> coe MAlonzo.Code.Once.IR.C_inr_62
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v15 v16
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v17 v18
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                     (d_optimize'45'compose_740
                                        (coe v17) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v9) (coe v1))
                                        (coe MAlonzo.Code.Once.IR.C_inr_62) (coe v15))
                                     (d_optimize'45'compose_740
                                        (coe v18) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v9) (coe v1))
                                        (coe MAlonzo.Code.Once.IR.C_inr_62) (coe v16))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_84
                         -> coe MAlonzo.Code.Once.IR.C_initial_84
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__40 v12 v13
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_10
                         -> coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v10 v11
                       MAlonzo.Code.Once.IR.C_inl_54 -> coe v10
                       MAlonzo.Code.Once.IR.C_inr_62 -> coe v11
                       MAlonzo.Code.Once.IR.C_initial_84
                         -> coe MAlonzo.Code.Once.IR.C_initial_84
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_terminal_78
           -> case coe v4 of
                MAlonzo.Code.Once.IR.C_id_10
                  -> coe MAlonzo.Code.Once.IR.C_terminal_78
                MAlonzo.Code.Once.IR.C__'8728'__20 v10 v12 v13
                  -> coe MAlonzo.Code.Once.IR.C_terminal_78
                MAlonzo.Code.Once.IR.C_fst_28
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'42'__38 v11 v12
                         -> coe MAlonzo.Code.Once.IR.C_terminal_78
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_snd_36
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'42'__38 v11 v12
                         -> coe MAlonzo.Code.Once.IR.C_terminal_78
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v12 v13
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'42'__38 v14 v15
                         -> coe MAlonzo.Code.Once.IR.C_terminal_78
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_inl_54
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'43'__40 v11 v12
                         -> coe MAlonzo.Code.Once.IR.C_terminal_78
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_inr_62
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'43'__40 v11 v12
                         -> coe MAlonzo.Code.Once.IR.C_terminal_78
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v12 v13
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'43'__40 v14 v15
                         -> coe MAlonzo.Code.Once.IR.C_terminal_78
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_terminal_78
                  -> coe MAlonzo.Code.Once.IR.C_terminal_78
                MAlonzo.Code.Once.IR.C_initial_84
                  -> coe MAlonzo.Code.Once.IR.C_initial_84
                MAlonzo.Code.Once.IR.C_curry_94 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v13 v14 v15
                         -> coe MAlonzo.Code.Once.IR.C_terminal_78
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_apply_102
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'42'__38 v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v13 v14 v15
                                -> coe MAlonzo.Code.Once.IR.C_terminal_78
                              _ -> coe v5
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_fold_108
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C_Fix_46 v10
                         -> coe MAlonzo.Code.Once.IR.C_terminal_78
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_unfold_114
                  -> coe MAlonzo.Code.Once.IR.C_terminal_78
                MAlonzo.Code.Once.IR.C_arr_122
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v11 v12 v13
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C_Eff_44 v14 v15
                                -> coe MAlonzo.Code.Once.IR.C_terminal_78
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.IR.C_curry_94 v10
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v11 v12 v13
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_10
                         -> coe MAlonzo.Code.Once.IR.C_curry_94 v10
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v18 v19
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v20 v21
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                     (d_optimize'45'compose_740
                                        (coe v20) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 (coe v11)
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                                        (coe MAlonzo.Code.Once.IR.C_curry_94 v10) (coe v18))
                                     (d_optimize'45'compose_740
                                        (coe v21) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 (coe v11)
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                                        (coe MAlonzo.Code.Once.IR.C_curry_94 v10) (coe v19))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_84
                         -> coe MAlonzo.Code.Once.IR.C_initial_84
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_apply_102
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
                  -> case coe v9 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v11 v12 v13
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C_id_10
                                -> coe MAlonzo.Code.Once.IR.C_apply_102
                              MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v18 v19
                                -> case coe v0 of
                                     MAlonzo.Code.Once.Type.C__'43'__40 v20 v21
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                            (d_optimize'45'compose_740
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__38
                                                  (coe
                                                     MAlonzo.Code.Once.Type.d__'8658'__64 (coe v11)
                                                     (coe v2))
                                                  (coe v11))
                                               (coe v2) (coe MAlonzo.Code.Once.IR.C_apply_102)
                                               (coe v18))
                                            (d_optimize'45'compose_740
                                               (coe v21)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__38
                                                  (coe
                                                     MAlonzo.Code.Once.Type.d__'8658'__64 (coe v11)
                                                     (coe v2))
                                                  (coe v11))
                                               (coe v2) (coe MAlonzo.Code.Once.IR.C_apply_102)
                                               (coe v19))
                                     _ -> coe v5
                              MAlonzo.Code.Once.IR.C_initial_84
                                -> coe MAlonzo.Code.Once.IR.C_initial_84
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_fold_108
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_Fix_46 v8
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_id_10 -> coe MAlonzo.Code.Once.IR.C_fold_108
                       MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v13 v14
                         -> case coe v0 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v15 v16
                                -> coe
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                     (d_optimize'45'compose_740
                                        (coe v15) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v1))
                                        (coe MAlonzo.Code.Once.IR.C_fold_108) (coe v13))
                                     (d_optimize'45'compose_740
                                        (coe v16) (coe v1)
                                        (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v1))
                                        (coe MAlonzo.Code.Once.IR.C_fold_108) (coe v14))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_initial_84
                         -> coe MAlonzo.Code.Once.IR.C_initial_84
                       MAlonzo.Code.Once.IR.C_unfold_114
                         -> coe MAlonzo.Code.Once.IR.C_id_10
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_unfold_114
           -> case coe v4 of
                MAlonzo.Code.Once.IR.C_id_10
                  -> coe MAlonzo.Code.Once.IR.C_unfold_114
                MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v12 v13
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'43'__40 v14 v15
                         -> coe
                              MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                              (d_optimize'45'compose_740
                                 (coe v14) (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v2)) (coe v2)
                                 (coe MAlonzo.Code.Once.IR.C_unfold_114) (coe v12))
                              (d_optimize'45'compose_740
                                 (coe v15) (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v2)) (coe v2)
                                 (coe MAlonzo.Code.Once.IR.C_unfold_114) (coe v13))
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_initial_84
                  -> coe MAlonzo.Code.Once.IR.C_initial_84
                MAlonzo.Code.Once.IR.C_fold_108 -> coe MAlonzo.Code.Once.IR.C_id_10
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_arr_122
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Once.Type.C_Eff_44 v12 v13
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C_id_10 -> coe MAlonzo.Code.Once.IR.C_arr_122
                              MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v18 v19
                                -> case coe v0 of
                                     MAlonzo.Code.Once.Type.C__'43'__40 v20 v21
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                            (d_optimize'45'compose_740
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Type.d__'8658'__64 (coe v9)
                                                  (coe v11))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_Eff_44 (coe v9)
                                                  (coe v11))
                                               (coe MAlonzo.Code.Once.IR.C_arr_122) (coe v18))
                                            (d_optimize'45'compose_740
                                               (coe v21)
                                               (coe
                                                  MAlonzo.Code.Once.Type.d__'8658'__64 (coe v9)
                                                  (coe v11))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_Eff_44 (coe v9)
                                                  (coe v11))
                                               (coe MAlonzo.Code.Once.IR.C_arr_122) (coe v19))
                                     _ -> coe v5
                              MAlonzo.Code.Once.IR.C_initial_84
                                -> coe MAlonzo.Code.Once.IR.C_initial_84
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         _ -> coe v5)
-- Once.Optimize.optimize-pair
d_optimize'45'pair_922 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'pair_922 v0 v1 v2 v3 v4
  = let v5
          = coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v3 v4 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C__'8728'__20 v8 v10 v11
           -> case coe v10 of
                MAlonzo.Code.Once.IR.C_fst_28
                  -> case coe v8 of
                       MAlonzo.Code.Once.Type.C__'42'__38 v15 v16
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C__'8728'__20 v19 v21 v22
                                -> case coe v21 of
                                     MAlonzo.Code.Once.IR.C_snd_36
                                       -> case coe v19 of
                                            MAlonzo.Code.Once.Type.C__'42'__38 v26 v27
                                              -> let v28 = d__'8799'Type__8 (coe v0) (coe v26) in
                                                 coe
                                                   (let v29 = d__'8799'Type__8 (coe v16) (coe v1) in
                                                    coe
                                                      (case coe v28 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                           -> let v32
                                                                    = coe
                                                                        MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                                                        (coe
                                                                           MAlonzo.Code.Once.IR.C__'8728'__20
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'42'__38
                                                                              (coe v0) (coe v16))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_fst_28)
                                                                           v11)
                                                                        (coe
                                                                           MAlonzo.Code.Once.IR.C__'8728'__20
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'42'__38
                                                                              (coe v26) (coe v1))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_snd_36)
                                                                           v22) in
                                                              coe
                                                                (case coe v30 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v31 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v33
                                                                            -> case coe v29 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                   -> case coe
                                                                                             v34 of
                                                                                        MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                          -> case coe
                                                                                                    v35 of
                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                 -> let v37
                                                                                                          = d__'8799'IR__508
                                                                                                              (coe
                                                                                                                 v2)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.Type.C__'42'__38
                                                                                                                 (coe
                                                                                                                    v0)
                                                                                                                 (coe
                                                                                                                    v1))
                                                                                                              (coe
                                                                                                                 v11)
                                                                                                              (coe
                                                                                                                 v22) in
                                                                                                    coe
                                                                                                      (case coe
                                                                                                              v37 of
                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v38 v39
                                                                                                           -> if coe
                                                                                                                   v38
                                                                                                                then coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v39)
                                                                                                                       (coe
                                                                                                                          v11)
                                                                                                                else coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v39)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.IR.C__'8728'__20
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Type.C__'42'__38
                                                                                                                                (coe
                                                                                                                                   v0)
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.IR.C_fst_28)
                                                                                                                             v11)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.IR.C__'8728'__20
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Type.C__'42'__38
                                                                                                                                (coe
                                                                                                                                   v0)
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.IR.C_snd_36)
                                                                                                                             v22))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                               _ -> coe
                                                                                                      v32
                                                                                        _ -> coe v32
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> coe v32
                                                                   _ -> coe v32)
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_fst_28
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_snd_36
                         -> let v14 = d__'8799'Type__8 (coe v0) (coe v0) in
                            coe
                              (let v15 = d__'8799'Type__8 (coe v1) (coe v1) in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                      -> let v18
                                               = coe
                                                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                                                   (coe MAlonzo.Code.Once.IR.C_fst_28)
                                                   (coe MAlonzo.Code.Once.IR.C_snd_36) in
                                         coe
                                           (case coe v16 of
                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                -> case coe v17 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                       -> case coe v15 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                              -> case coe v20 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v21 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                                            -> coe
                                                                                 MAlonzo.Code.Once.IR.C_id_10
                                                                          _ -> coe v18
                                                                   _ -> coe v18
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v18
                                              _ -> coe v18)
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> coe v5
                _ -> coe v5
         _ -> coe v5)
-- Once.Optimize.optimize-case
d_optimize'45'case_1046 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_4 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'case_1046 v0 v1 v2 v3 v4
  = let v5 = coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v3 v4 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C__'8728'__20 v8 v10 v11
           -> case coe v11 of
                MAlonzo.Code.Once.IR.C_inl_54
                  -> case coe v8 of
                       MAlonzo.Code.Once.Type.C__'43'__40 v15 v16
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C__'8728'__20 v19 v21 v22
                                -> case coe v22 of
                                     MAlonzo.Code.Once.IR.C_inr_62
                                       -> case coe v19 of
                                            MAlonzo.Code.Once.Type.C__'43'__40 v26 v27
                                              -> let v28 = d__'8799'Type__8 (coe v0) (coe v26) in
                                                 coe
                                                   (let v29 = d__'8799'Type__8 (coe v16) (coe v1) in
                                                    coe
                                                      (case coe v28 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                           -> let v32
                                                                    = coe
                                                                        MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                                                        (coe
                                                                           MAlonzo.Code.Once.IR.C__'8728'__20
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'43'__40
                                                                              (coe v0) (coe v16))
                                                                           v10
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_inl_54))
                                                                        (coe
                                                                           MAlonzo.Code.Once.IR.C__'8728'__20
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'43'__40
                                                                              (coe v26) (coe v1))
                                                                           v21
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_inr_62)) in
                                                              coe
                                                                (case coe v30 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v31 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v33
                                                                            -> case coe v29 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                   -> case coe
                                                                                             v34 of
                                                                                        MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                          -> case coe
                                                                                                    v35 of
                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                 -> let v37
                                                                                                          = d__'8799'IR__508
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.Type.C__'43'__40
                                                                                                                 (coe
                                                                                                                    v0)
                                                                                                                 (coe
                                                                                                                    v1))
                                                                                                              (coe
                                                                                                                 v2)
                                                                                                              (coe
                                                                                                                 v10)
                                                                                                              (coe
                                                                                                                 v21) in
                                                                                                    coe
                                                                                                      (case coe
                                                                                                              v37 of
                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v38 v39
                                                                                                           -> if coe
                                                                                                                   v38
                                                                                                                then coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v39)
                                                                                                                       (coe
                                                                                                                          v10)
                                                                                                                else coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v39)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.IR.C__'8728'__20
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Type.C__'43'__40
                                                                                                                                (coe
                                                                                                                                   v0)
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                             v10
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.IR.C_inl_54))
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.IR.C__'8728'__20
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Type.C__'43'__40
                                                                                                                                (coe
                                                                                                                                   v0)
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                             v21
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.IR.C_inr_62)))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                               _ -> coe
                                                                                                      v32
                                                                                        _ -> coe v32
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> coe v32
                                                                   _ -> coe v32)
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inl_54
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__40 v9 v10
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_inr_62
                         -> let v14 = d__'8799'Type__8 (coe v0) (coe v0) in
                            coe
                              (let v15 = d__'8799'Type__8 (coe v1) (coe v1) in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                      -> let v18
                                               = coe
                                                   MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                                                   (coe MAlonzo.Code.Once.IR.C_inl_54)
                                                   (coe MAlonzo.Code.Once.IR.C_inr_62) in
                                         coe
                                           (case coe v16 of
                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                -> case coe v17 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                       -> case coe v15 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                              -> case coe v20 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v21 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                                            -> coe
                                                                                 MAlonzo.Code.Once.IR.C_id_10
                                                                          _ -> coe v18
                                                                   _ -> coe v18
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v18
                                              _ -> coe v18)
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> coe v5
                _ -> coe v5
         _ -> coe v5)
-- Once.Optimize.optimize-once
d_optimize'45'once_1168 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'once_1168 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_10 -> coe MAlonzo.Code.Once.IR.C_id_10
      MAlonzo.Code.Once.IR.C__'8728'__20 v5 v7 v8
        -> coe
             d_optimize'45'compose_740 (coe v0) (coe v5) (coe v1)
             (coe d_optimize'45'once_1168 (coe v5) (coe v1) (coe v7))
             (coe d_optimize'45'once_1168 (coe v0) (coe v5) (coe v8))
      MAlonzo.Code.Once.IR.C_fst_28 -> coe MAlonzo.Code.Once.IR.C_fst_28
      MAlonzo.Code.Once.IR.C_snd_36 -> coe MAlonzo.Code.Once.IR.C_snd_36
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    d_optimize'45'pair_922 (coe v9) (coe v10) (coe v0)
                    (coe d_optimize'45'once_1168 (coe v0) (coe v9) (coe v7))
                    (coe d_optimize'45'once_1168 (coe v0) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_54 -> coe MAlonzo.Code.Once.IR.C_inl_54
      MAlonzo.Code.Once.IR.C_inr_62 -> coe MAlonzo.Code.Once.IR.C_inr_62
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v9 v10
               -> coe
                    d_optimize'45'case_1046 (coe v9) (coe v10) (coe v1)
                    (coe d_optimize'45'once_1168 (coe v9) (coe v1) (coe v7))
                    (coe d_optimize'45'once_1168 (coe v10) (coe v1) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_78
        -> coe MAlonzo.Code.Once.IR.C_terminal_78
      MAlonzo.Code.Once.IR.C_initial_84
        -> coe MAlonzo.Code.Once.IR.C_initial_84
      MAlonzo.Code.Once.IR.C_curry_94 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_94
                    (d_optimize'45'once_1168
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v8))
                       (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_102
        -> coe MAlonzo.Code.Once.IR.C_apply_102
      MAlonzo.Code.Once.IR.C_fold_108
        -> coe MAlonzo.Code.Once.IR.C_fold_108
      MAlonzo.Code.Once.IR.C_unfold_114
        -> coe MAlonzo.Code.Once.IR.C_unfold_114
      MAlonzo.Code.Once.IR.C_arr_122
        -> coe MAlonzo.Code.Once.IR.C_arr_122
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-n
d_optimize'45'n_1188 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize'45'n_1188 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_1188 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_1168 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_1200 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_optimize_1200 v0 v1
  = coe d_optimize'45'n_1188 (coe v0) (coe v1) (coe (10 :: Integer))
