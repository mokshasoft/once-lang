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

module MAlonzo.Code.Once.TypeCheck.Elaborate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Elaborate._≟F_
d__'8799'F__10 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__10 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_40 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_40 v3
               -> let v4 = d__'8799'T__16 (coe v2) (coe v3) in
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
             MAlonzo.Code.Once.Type.C_Id_42
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__44 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__46 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Id_42
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_40 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_42
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'8853'__44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__46 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8853'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_40 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_42
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__44 v4 v5
               -> let v6 = d__'8799'F__10 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'F__10 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C__'8855'__46 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__46 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_40 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_42
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__44 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__46 v4 v5
               -> let v6 = d__'8799'F__10 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'F__10 (coe v3) (coe v5) in
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
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._≟T_
d__'8799'T__16 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'T__16 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_48
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Void_50
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'42'__52 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'42'__52 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v4 v5
               -> let v6 = d__'8799'T__16 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__16 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C__'43'__54 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__54 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v4 v5
               -> let v6 = d__'8799'T__16 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__16 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v5 v6 v7
               -> let v8 = d__'8799'T__16 (coe v2) (coe v5) in
                  coe
                    (let v9
                           = MAlonzo.Code.Once.Type.d__'8799'q__26 (coe v3) (coe v6) in
                     coe
                       (let v10 = d__'8799'T__16 (coe v4) (coe v7) in
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
             MAlonzo.Code.Once.Type.C_Eff_58 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Eff_58 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v4 v5
               -> let v6 = d__'8799'T__16 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__16 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_60 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v3
               -> let v4 = d__'8799'F__10 (coe v2) (coe v3) in
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
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_ν'45'type_62 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v3
               -> let v4 = d__'8799'F__10 (coe v2) (coe v3) in
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
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_64
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Float_66
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Str_68
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Buffer_70
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__52 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_58 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.InferElabResult
d_InferElabResult_378 a0 a1 = ()
data T_InferElabResult_378
  = C_success_392 MAlonzo.Code.Once.Type.T_Type_38
                  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_failure_394 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_402 a0 a1 a2 = ()
data T_CheckElabResult_402
  = C_success_416 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_failure_418 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.Imports
d_Imports_420 :: ()
d_Imports_420 = erased
-- Once.TypeCheck.Elaborate.emptyImports
d_emptyImports_422 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyImports_422
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Elaborate.NamedCtx
d_NamedCtx_424 = ()
data T_NamedCtx_424
  = C_mkCtx_446 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 Integer
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Elaborate.NamedCtx.size
d_size_436 :: T_NamedCtx_424 -> Integer
d_size_436 v0
  = case coe v0 of
      C_mkCtx_446 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.named
d_named_438 ::
  T_NamedCtx_424 -> [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_438 v0
  = case coe v0 of
      C_mkCtx_446 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.debruijn
d_debruijn_440 ::
  T_NamedCtx_424 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_440 v0
  = case coe v0 of
      C_mkCtx_446 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.freshCounter
d_freshCounter_442 :: T_NamedCtx_424 -> Integer
d_freshCounter_442 v0
  = case coe v0 of
      C_mkCtx_446 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.imports
d_imports_444 ::
  T_NamedCtx_424 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_444 v0
  = case coe v0 of
      C_mkCtx_446 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.emptyCtx
d_emptyCtx_448 :: T_NamedCtx_424
d_emptyCtx_448
  = coe
      C_mkCtx_446 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe d_emptyImports_422)
-- Once.TypeCheck.Elaborate.ctxWithImports
d_ctxWithImports_450 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_424
d_ctxWithImports_450 v0
  = coe
      C_mkCtx_446 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0)
-- Once.TypeCheck.Elaborate.ctxWithImportsAndSelf
d_ctxWithImportsAndSelf_454 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_NamedCtx_424
d_ctxWithImportsAndSelf_454 v0 v1 v2
  = coe
      d_ctxWithImports_450
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
         (coe v0))
-- Once.TypeCheck.Elaborate.extendNamedCtx
d_extendNamedCtx_462 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_NamedCtx_424
d_extendNamedCtx_462 v0 v1 v2
  = case coe v0 of
      C_mkCtx_446 v3 v4 v5 v6 v7
        -> coe
             C_mkCtx_446 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v5) (coe v2))
             (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.bumpFresh
d_bumpFresh_478 :: T_NamedCtx_424 -> T_NamedCtx_424
d_bumpFresh_478 v0
  = case coe v0 of
      C_mkCtx_446 v1 v2 v3 v4 v5
        -> coe
             C_mkCtx_446 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.freshTVar
d_freshTVar_490 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_490 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Elaborate.specId
d_specId_496 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specId_496 ~v0 = du_specId_496
du_specId_496 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specId_496
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_var_182
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.TypeCheck.Elaborate.specFst
d_specFst_504 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specFst_504 ~v0 v1 = du_specFst_504 v1
du_specFst_504 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specFst_504 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v0
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_514 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specSnd_514 v0 ~v1 = du_specSnd_514 v0
du_specSnd_514 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specSnd_514 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v0
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specInl
d_specInl_524 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specInl_524 ~v0 ~v1 = du_specInl_524
du_specInl_524 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specInl_524
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_inl''_278
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specInr
d_specInr_534 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specInr_534 ~v0 ~v1 = du_specInr_534
du_specInr_534 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specInr_534
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_inr''_290
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_540 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specUnitGen_540 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318
-- Once.TypeCheck.Elaborate.specPair
d_specPair_548 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specPair_548 v0 ~v1 ~v2 = du_specPair_548 v0
du_specPair_548 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specPair_548 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe
            MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_Zero_6)))
         (coe
            MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_Zero_6))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_198
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)))
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_One_8)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_198
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_pair_242
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specTerminal
d_specTerminal_558 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specTerminal_558 ~v0 = du_specTerminal_558
du_specTerminal_558 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specTerminal_558
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_Zero_6)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_564 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specInitial_564 ~v0 = du_specInitial_564
du_specInitial_564 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specInitial_564
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_absurd_328
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_574 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specCurry_574 v0 v1 ~v2 = du_specCurry_574 v0 v1
du_specCurry_574 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specCurry_574 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe MAlonzo.Code.Once.Type.C_Zero_6))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_198
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_198
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe MAlonzo.Code.Once.Type.C_One_8))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_app_214
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe MAlonzo.Code.Once.Type.C_One_8))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6))
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_182
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_pair_242
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specApply
d_specApply_586 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specApply_586 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_One_8)))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_214
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))
         v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v0
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_182
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_snd''_266
            (MAlonzo.Code.Once.Type.d__'8658'__78 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_182
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.TypeCheck.Elaborate.specCompose
d_specCompose_598 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specCompose_598 v0 v1 ~v2 = du_specCompose_598 v0 v1
du_specCompose_598 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specCompose_598 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_198
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_198
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_app_214
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_182
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specArr
d_specArr_610 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specArr_610 ~v0 ~v1 = du_specArr_610
du_specArr_610 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specArr_610
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_arr''_486
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.lookupImport
d_lookupImport_616 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_38
d_lookupImport_616 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v4))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                               (coe v1)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupImport_616 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_646 = ()
data T_AppSpine_646
  = C_mkSpine_656 MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_652 ::
  T_AppSpine_646 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_head_652 v0
  = case coe v0 of
      C_mkSpine_656 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_654 ::
  T_AppSpine_646 -> [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
d_args_654 v0
  = case coe v0 of
      C_mkSpine_656 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_658 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppSpine_646
d_spineOf_658 v0
  = coe
      du_go_666 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_666 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_646
d_go_666 ~v0 v1 v2 = du_go_666 v1 v2
du_go_666 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_646
du_go_666 v0 v1
  = let v2 = coe C_mkSpine_656 (coe v0) (coe v1) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v3 v4
           -> coe
                du_go_666 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v1))
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_678 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_678 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         l | (==) l ("apply" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("arr" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("compose" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("curry" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("id" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("initial" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("terminal" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("unit" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.lookupLocal
d_lookupLocal_686 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal_686 v0 v1
  = case coe v0 of
      C_mkCtx_446 v2 v3 v4 v5 v6
        -> coe du_go_708 (coe v1) (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_708 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_708 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_708 v5 v6 v7 v8
du_go_708 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_708 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v7 v8 v9
               -> let v10 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (let v11
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v0))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_14 (coe v4))) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                            -> if coe v12
                                 then coe
                                        seq (coe v13)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Syntax.d_singleUse_66
                                                    (coe v1)
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                    (coe MAlonzo.Code.Once.Type.C_One_8))
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Syntax.C_var_182
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                 else coe
                                        seq (coe v13)
                                        (let v14
                                               = coe
                                                   du_go_708 (coe v0) (coe v10) (coe v5) (coe v7) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                -> case coe v15 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                       -> case coe v17 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v16)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_Zero_6)
                                                                            v18)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Thinning.du_weaken_900
                                                                            (coe v7) (coe v8)
                                                                            (coe v16) (coe v9)
                                                                            (coe v19))))
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe v14
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.findLocalVarUsage
d_findLocalVarUsage_776 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findLocalVarUsage_776 v0 v1
  = case coe v0 of
      C_mkCtx_446 v2 v3 v4 v5 v6
        -> coe du_go_792 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_792 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_792 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 = du_go_792 v5 v7 v8
du_go_792 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_792 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v6 v7 v8
               -> let v9
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v9 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_14 (coe v3))) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v8)))
                              else coe
                                     seq (coe v11)
                                     (let v12 = coe du_go_792 (coe v0) (coe v4) (coe v6) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                             -> case coe v13 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                               v14)
                                                            (coe v15))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.matchInferResult
d_matchInferResult_862 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_InferElabResult_378 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
d_matchInferResult_862 ~v0 ~v1 v2 v3
  = du_matchInferResult_862 v2 v3
du_matchInferResult_862 ::
  T_InferElabResult_378 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
du_matchInferResult_862 v0 v1
  = case coe v0 of
      C_success_392 v2 v3 v4 v5 v6
        -> let v7 = d__'8799'T__16 (coe v1) (coe v2) in
           coe
             (case coe v7 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                  -> if coe v8
                       then coe
                              seq (coe v9)
                              (coe C_success_416 (coe v3) (coe v4) (coe v5) (coe v6))
                       else coe
                              seq (coe v9)
                              (coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50 (coe v1)
                                    (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_394 v2 -> coe C_failure_418 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.FunProjection
d_FunProjection_910 a0 a1 = ()
data T_FunProjection_910
  = C_isFun_924 MAlonzo.Code.Once.Type.T_Type_38
                MAlonzo.Code.Once.Type.T_Quantity_4
                MAlonzo.Code.Once.Type.T_Type_38
                MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_isEff_932 MAlonzo.Code.Once.Type.T_Type_38
                MAlonzo.Code.Once.Type.T_Type_38
                MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_notFun_934 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asFun
d_asFun_940 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_InferElabResult_378 -> T_FunProjection_910
d_asFun_940 ~v0 ~v1 v2 = du_asFun_940 v2
du_asFun_940 :: T_InferElabResult_378 -> T_FunProjection_910
du_asFun_940 v0
  = case coe v0 of
      C_success_392 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__52 v6 v7
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__54 v6 v7
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v6 v7 v8
               -> coe
                    C_isFun_924 (coe v6) (coe v7) (coe v8) (coe v2) (coe v3) (coe v4)
                    (coe v5)
             MAlonzo.Code.Once.Type.C_Eff_58 v6 v7
               -> coe
                    C_isEff_932 (coe v6) (coe v7) (coe v2) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v6
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v6
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    C_notFun_934
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_54 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_394 v1 -> coe C_notFun_934 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_998 a0 a1 = ()
data T_IntProjection_998
  = C_isInt_1006 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_notInt_1008 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1014 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_InferElabResult_378 -> T_IntProjection_998
d_asInt_1014 ~v0 ~v1 v2 = du_asInt_1014 v2
du_asInt_1014 :: T_InferElabResult_378 -> T_IntProjection_998
du_asInt_1014 v0
  = case coe v0 of
      C_success_392 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__52 v6 v7
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__54 v6 v7
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v6 v7 v8
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Eff_58 v6 v7
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v6
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v6
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe C_isInt_1006 (coe v2) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    C_notInt_1008
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_394 v1 -> coe C_notInt_1008 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.decideLeq
d_decideLeq_1052 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1052 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Zero_6
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased)
      MAlonzo.Code.Once.Type.C_One_8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_One_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Many_10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_One_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.PolyBuiltinApp
d_PolyBuiltinApp_1054 = ()
data T_PolyBuiltinApp_1054
  = C_pba'45'id_1056 | C_pba'45'fst_1058 | C_pba'45'snd_1060 |
    C_pba'45'terminal_1062 | C_pba'45'inl_1064 | C_pba'45'inr_1066 |
    C_pba'45'initial_1068
-- Once.TypeCheck.Elaborate.classifyAppHead
d_classifyAppHead_1070 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe T_PolyBuiltinApp_1054
d_classifyAppHead_1070 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
           -> let v3
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v3 ->
                           coe
                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                             (coe v2))
                        (coe
                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v2)
                           (coe ("id" :: Data.Text.Text))) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                     -> if coe v4
                          then coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe C_pba'45'id_1056))
                          else coe
                                 seq (coe v5)
                                 (let v6
                                        = coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                            erased
                                            (\ v6 ->
                                               coe
                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                 (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                               (coe v2) (coe ("fst" :: Data.Text.Text))) in
                                  coe
                                    (case coe v6 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                         -> if coe v7
                                              then coe
                                                     seq (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                        (coe C_pba'45'fst_1058))
                                              else coe
                                                     seq (coe v8)
                                                     (let v9
                                                            = coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                erased
                                                                (\ v9 ->
                                                                   coe
                                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                     (coe v2))
                                                                (coe
                                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                   (coe v2)
                                                                   (coe
                                                                      ("snd" :: Data.Text.Text))) in
                                                      coe
                                                        (case coe v9 of
                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                             -> if coe v10
                                                                  then coe
                                                                         seq (coe v11)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                            (coe C_pba'45'snd_1060))
                                                                  else coe
                                                                         seq (coe v11)
                                                                         (let v12
                                                                                = coe
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                    erased
                                                                                    (\ v12 ->
                                                                                       coe
                                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                         (coe v2))
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                       (coe v2)
                                                                                       (coe
                                                                                          ("terminal"
                                                                                           ::
                                                                                           Data.Text.Text))) in
                                                                          coe
                                                                            (case coe v12 of
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                                                 -> if coe v13
                                                                                      then coe
                                                                                             seq
                                                                                             (coe
                                                                                                v14)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                (coe
                                                                                                   C_pba'45'terminal_1062))
                                                                                      else coe
                                                                                             seq
                                                                                             (coe
                                                                                                v14)
                                                                                             (let v15
                                                                                                    = coe
                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                        erased
                                                                                                        (\ v15 ->
                                                                                                           coe
                                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                             (coe
                                                                                                                v2))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                           (coe
                                                                                                              v2)
                                                                                                           (coe
                                                                                                              ("inl"
                                                                                                               ::
                                                                                                               Data.Text.Text))) in
                                                                                              coe
                                                                                                (case coe
                                                                                                        v15 of
                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                                     -> if coe
                                                                                                             v16
                                                                                                          then coe
                                                                                                                 seq
                                                                                                                 (coe
                                                                                                                    v17)
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                    (coe
                                                                                                                       C_pba'45'inl_1064))
                                                                                                          else coe
                                                                                                                 seq
                                                                                                                 (coe
                                                                                                                    v17)
                                                                                                                 (let v18
                                                                                                                        = coe
                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                            erased
                                                                                                                            (\ v18 ->
                                                                                                                               coe
                                                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                 (coe
                                                                                                                                    v2))
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                               (coe
                                                                                                                                  v2)
                                                                                                                               (coe
                                                                                                                                  ("inr"
                                                                                                                                   ::
                                                                                                                                   Data.Text.Text))) in
                                                                                                                  coe
                                                                                                                    (case coe
                                                                                                                            v18 of
                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                                                         -> if coe
                                                                                                                                 v19
                                                                                                                              then coe
                                                                                                                                     seq
                                                                                                                                     (coe
                                                                                                                                        v20)
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                        (coe
                                                                                                                                           C_pba'45'inr_1066))
                                                                                                                              else coe
                                                                                                                                     seq
                                                                                                                                     (coe
                                                                                                                                        v20)
                                                                                                                                     (let v21
                                                                                                                                            = coe
                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                erased
                                                                                                                                                (\ v21 ->
                                                                                                                                                   coe
                                                                                                                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                     (coe
                                                                                                                                                        v2))
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                   (coe
                                                                                                                                                      v2)
                                                                                                                                                   (coe
                                                                                                                                                      ("initial"
                                                                                                                                                       ::
                                                                                                                                                       Data.Text.Text))) in
                                                                                                                                      coe
                                                                                                                                        (case coe
                                                                                                                                                v21 of
                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                                                             -> if coe
                                                                                                                                                     v22
                                                                                                                                                  then coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v23)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                            (coe
                                                                                                                                                               C_pba'45'initial_1068))
                                                                                                                                                  else coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v23)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.AppHeadView
d_AppHeadView_1130 a0 = ()
data T_AppHeadView_1130
  = C_ahv'45'id_1132 | C_ahv'45'fst_1134 | C_ahv'45'snd_1136 |
    C_ahv'45'terminal_1138 | C_ahv'45'inl_1140 | C_ahv'45'inr_1142 |
    C_ahv'45'initial_1144 | C_ahv'45'other_1148
-- Once.TypeCheck.Elaborate.classifyAppHeadView
d_classifyAppHeadView_1152 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppHeadView_1130
d_classifyAppHeadView_1152 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v1
        -> let v2
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v2 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                        (coe ("id" :: Data.Text.Text))) in
           coe
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
                  -> if coe v3
                       then coe seq (coe v4) (coe C_ahv'45'id_1132)
                       else coe
                              seq (coe v4)
                              (let v5
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                              (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                            (coe v1) (coe ("fst" :: Data.Text.Text))) in
                               coe
                                 (case coe v5 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                                      -> if coe v6
                                           then coe seq (coe v7) (coe C_ahv'45'fst_1134)
                                           else coe
                                                  seq (coe v7)
                                                  (let v8
                                                         = coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                             erased
                                                             (\ v8 ->
                                                                coe
                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                  (coe v1))
                                                             (coe
                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                (coe v1)
                                                                (coe ("snd" :: Data.Text.Text))) in
                                                   coe
                                                     (case coe v8 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                          -> if coe v9
                                                               then coe
                                                                      seq (coe v10)
                                                                      (coe C_ahv'45'snd_1136)
                                                               else coe
                                                                      seq (coe v10)
                                                                      (let v11
                                                                             = coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                 erased
                                                                                 (\ v11 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                      (coe v1))
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                    (coe v1)
                                                                                    (coe
                                                                                       ("terminal"
                                                                                        ::
                                                                                        Data.Text.Text))) in
                                                                       coe
                                                                         (case coe v11 of
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                                              -> if coe v12
                                                                                   then coe
                                                                                          seq
                                                                                          (coe v13)
                                                                                          (coe
                                                                                             C_ahv'45'terminal_1138)
                                                                                   else coe
                                                                                          seq
                                                                                          (coe v13)
                                                                                          (let v14
                                                                                                 = coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                     erased
                                                                                                     (\ v14 ->
                                                                                                        coe
                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                          (coe
                                                                                                             v1))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                        (coe
                                                                                                           v1)
                                                                                                        (coe
                                                                                                           ("inl"
                                                                                                            ::
                                                                                                            Data.Text.Text))) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v14 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                                                  -> if coe
                                                                                                          v15
                                                                                                       then coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v16)
                                                                                                              (coe
                                                                                                                 C_ahv'45'inl_1140)
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v16)
                                                                                                              (let v17
                                                                                                                     = coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                         erased
                                                                                                                         (\ v17 ->
                                                                                                                            coe
                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                              (coe
                                                                                                                                 v1))
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                            (coe
                                                                                                                               v1)
                                                                                                                            (coe
                                                                                                                               ("inr"
                                                                                                                                ::
                                                                                                                                Data.Text.Text))) in
                                                                                                               coe
                                                                                                                 (case coe
                                                                                                                         v17 of
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                                      -> if coe
                                                                                                                              v18
                                                                                                                           then coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v19)
                                                                                                                                  (coe
                                                                                                                                     C_ahv'45'inr_1142)
                                                                                                                           else coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v19)
                                                                                                                                  (let v20
                                                                                                                                         = coe
                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                             erased
                                                                                                                                             (\ v20 ->
                                                                                                                                                coe
                                                                                                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                  (coe
                                                                                                                                                     v1))
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                (coe
                                                                                                                                                   v1)
                                                                                                                                                (coe
                                                                                                                                                   ("initial"
                                                                                                                                                    ::
                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                   coe
                                                                                                                                     (case coe
                                                                                                                                             v20 of
                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                                                                          -> if coe
                                                                                                                                                  v21
                                                                                                                                               then coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v22)
                                                                                                                                                      (coe
                                                                                                                                                         C_ahv'45'initial_1144)
                                                                                                                                               else coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v22)
                                                                                                                                                      (coe
                                                                                                                                                         C_ahv'45'other_1148)
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v1 v2
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v1 v2
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v1 v2 v3
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v1 v2
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v1
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v1
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v1 v2
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v1 v2 v3
        -> coe C_ahv'45'other_1148
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v2
        -> coe C_ahv'45'other_1148
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.classifyAppHead-nothing⇒view-other
d_classifyAppHead'45'nothing'8658'view'45'other_1214 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHead'45'nothing'8658'view'45'other_1214 = erased
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_1362 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_378
d_inferElab_1362 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v3 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v2))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v2)
                        (coe ("unit" :: Data.Text.Text))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then coe
                              seq (coe v5)
                              (coe
                                 C_success_392 (coe MAlonzo.Code.Once.Type.C_Unit_48)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                    (coe d_size_436 (coe v0)))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
                                 (coe (0 :: Integer)) (coe d_freshCounter_442 (coe v0)))
                       else coe
                              seq (coe v5)
                              (let v6
                                     = coe
                                         du_go_708 (coe v2) (coe d_size_436 (coe v0))
                                         (coe d_named_438 (coe v0)) (coe d_debruijn_440 (coe v0)) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                      -> case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                             -> case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                    -> coe
                                                         C_success_392 (coe v8) (coe v10) (coe v11)
                                                         (coe (0 :: Integer))
                                                         (coe d_freshCounter_442 (coe v0))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> let v7
                                               = d_lookupImport_616
                                                   (coe d_imports_444 (coe v0)) (coe v2) in
                                         coe
                                           (case coe v7 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                -> coe
                                                     C_success_392 (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                        (coe d_size_436 (coe v0)))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                        v2)
                                                     (coe (0 :: Integer))
                                                     (coe d_freshCounter_442 (coe v0))
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe
                                                     C_failure_394
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                        (coe v2))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> let v4
                 = d_lookupImport_616
                     (coe d_imports_444 (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("." :: Data.Text.Text) v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       C_success_392 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                          (coe d_size_436 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("." :: Data.Text.Text) v2)))
                       (coe (0 :: Integer)) (coe d_freshCounter_442 (coe v0))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_394
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_UnboundQualified_14 (coe v2)
                          (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v2 v3
        -> let v4 = d_classifyAppHeadView_1152 (coe v2) in
           coe
             (case coe v4 of
                C_ahv'45'id_1132
                  -> let v5 = d_inferElab_1362 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_392 v6 v7 v8 v9 v10
                            -> coe
                                 C_success_392 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_436 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                    (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_436 (coe v0)))
                                    v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                       (coe d_debruijn_440 (coe v0))
                                       (coe
                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v6)
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6))
                                       (coe du_specId_496))
                                    v8)
                                 (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'fst_1134
                  -> let v5 = d_inferElab_1362 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_392 v6 v7 v8 v9 v10
                            -> let v11
                                     = coe
                                         C_failure_394
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_30) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Once.Type.C__'42'__52 v12 v13
                                      -> coe
                                           C_success_392 (coe v12)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_436 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_436 (coe v0)))
                                              v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                 (coe d_debruijn_440 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                    (coe v6) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v12))
                                                 (coe du_specFst_504 (coe v13)))
                                              v8)
                                           (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                                    _ -> coe v11)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'snd_1136
                  -> let v5 = d_inferElab_1362 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_392 v6 v7 v8 v9 v10
                            -> let v11
                                     = coe
                                         C_failure_394
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_32) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Once.Type.C__'42'__52 v12 v13
                                      -> coe
                                           C_success_392 (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_436 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_436 (coe v0)))
                                              v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                 (coe d_debruijn_440 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                    (coe v6) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v13))
                                                 (coe du_specSnd_514 (coe v12)))
                                              v8)
                                           (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                                    _ -> coe v11)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'terminal_1138
                  -> let v5 = d_inferElab_1362 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_392 v6 v7 v8 v9 v10
                            -> coe
                                 C_success_392 (coe MAlonzo.Code.Once.Type.C_Unit_48)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_436 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                    (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_436 (coe v0)))
                                    v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                       (coe d_debruijn_440 (coe v0))
                                       (coe
                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v6)
                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                          (coe MAlonzo.Code.Once.Type.C_Unit_48))
                                       (coe du_specTerminal_558))
                                    v8)
                                 (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'inl_1140
                  -> coe
                       C_failure_394
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_20)
                C_ahv'45'inr_1142
                  -> coe
                       C_failure_394
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_22)
                C_ahv'45'initial_1144
                  -> coe
                       C_failure_394
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_24)
                C_ahv'45'other_1148
                  -> let v6
                           = coe du_asFun_940 (coe d_inferElab_1362 (coe v0) (coe v2)) in
                     coe
                       (case coe v6 of
                          C_isFun_924 v7 v8 v9 v10 v11 v12 v13
                            -> let v14 = d_inferElab_1362 (coe v0) (coe v3) in
                               coe
                                 (case coe v14 of
                                    C_success_392 v15 v16 v17 v18 v19
                                      -> let v20 = d__'8799'T__16 (coe v7) (coe v15) in
                                         coe
                                           (case coe v20 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                -> if coe v21
                                                     then coe
                                                            seq (coe v22)
                                                            (coe
                                                               C_success_392 (coe v9)
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                  (coe v10)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                     (coe v8) (coe v16)))
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                  v10 v16 v15 v8 v11 v17)
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v12) (coe v18))
                                                               (coe v19))
                                                     else coe
                                                            seq (coe v22)
                                                            (coe
                                                               C_failure_394
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_ApplicationTypeMismatch_44
                                                                  (coe v7) (coe v15)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v15 -> coe v14
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_isEff_932 v7 v8 v9 v10 v11 v12
                            -> let v13 = d_inferElab_1362 (coe v0) (coe v3) in
                               coe
                                 (case coe v13 of
                                    C_success_392 v14 v15 v16 v17 v18
                                      -> let v19 = d__'8799'T__16 (coe v7) (coe v14) in
                                         coe
                                           (case coe v19 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                -> if coe v20
                                                     then coe
                                                            seq (coe v21)
                                                            (coe
                                                               C_success_392
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Eff_58
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C_Unit_48)
                                                                  (coe v8))
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                  (coe v9) (coe v15))
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Syntax.C_effApp_228
                                                                  v9 v15 v14 v10 v16)
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v11) (coe v17))
                                                               (coe v18))
                                                     else coe
                                                            seq (coe v21)
                                                            (coe
                                                               C_failure_394
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_ApplicationTypeMismatch_44
                                                                  (coe v7) (coe v14)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v14 -> coe v13
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_notFun_934 v7 -> coe C_failure_394 (coe v7)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v2 v3
        -> coe
             C_failure_394
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_16)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v2 v3 v4
        -> let v5 = d_inferElab_1362 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_392 v6 v7 v8 v9 v10
                  -> let v11
                           = d_inferElab_1362
                               (coe d_extendNamedCtx_462 (coe v0) (coe v2) (coe v6)) (coe v4) in
                     coe
                       (case coe v11 of
                          C_success_392 v12 v13 v14 v15 v16
                            -> case coe v13 of
                                 MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v18 v19
                                   -> coe
                                        C_success_392 (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                           (coe v19)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                              (coe v18) (coe v7)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v7 v19 v18
                                           v6 v8 v14)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v9)
                                           (coe addInt (coe (1 :: Integer)) (coe v15)))
                                        (coe v16)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          C_failure_394 v12 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_394 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v2 v3
        -> let v4 = d_inferElab_1362 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_392 v5 v6 v7 v8 v9
                  -> let v10 = d_inferElab_1362 (coe v0) (coe v3) in
                     coe
                       (case coe v10 of
                          C_success_392 v11 v12 v13 v14 v15
                            -> coe
                                 C_success_392
                                 (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v5) (coe v11))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v6)
                                    (coe v12))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v6 v12 v7 v13)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v14))
                                 (coe v15)
                          C_failure_394 v11 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_394 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v2 v3 v4 v5 v6
        -> let v7 = d_inferElab_1362 (coe v0) (coe v2) in
           coe
             (case coe v7 of
                C_success_392 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               C_failure_394
                               (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_36) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Once.Type.C__'43'__54 v14 v15
                            -> let v16
                                     = d_inferElab_1362
                                         (coe d_extendNamedCtx_462 (coe v0) (coe v3) (coe v14))
                                         (coe v4) in
                               coe
                                 (case coe v16 of
                                    C_success_392 v17 v18 v19 v20 v21
                                      -> case coe v18 of
                                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v23 v24
                                             -> let v25
                                                      = d_inferElab_1362
                                                          (coe
                                                             d_extendNamedCtx_462 (coe v0) (coe v5)
                                                             (coe v15))
                                                          (coe v6) in
                                                coe
                                                  (case coe v25 of
                                                     C_success_392 v26 v27 v28 v29 v30
                                                       -> case coe v27 of
                                                            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v32 v33
                                                              -> let v34
                                                                       = d__'8799'T__16
                                                                           (coe v17) (coe v26) in
                                                                 coe
                                                                   (case coe v34 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v35 v36
                                                                        -> if coe v35
                                                                             then coe
                                                                                    seq (coe v36)
                                                                                    (coe
                                                                                       C_success_392
                                                                                       (coe v26)
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                          (coe v9)
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Syntax.du__'8852''7512'__104
                                                                                             (coe
                                                                                                v24)
                                                                                             (coe
                                                                                                v33)))
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_case''_312
                                                                                          v9 v24 v33
                                                                                          v23 v32
                                                                                          v14 v15
                                                                                          v10 v19
                                                                                          v28)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                             (coe
                                                                                                v11)
                                                                                             (coe
                                                                                                addInt
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v20)))
                                                                                          (coe
                                                                                             addInt
                                                                                             (coe
                                                                                                (1 ::
                                                                                                   Integer))
                                                                                             (coe
                                                                                                v29)))
                                                                                       (coe v30))
                                                                             else coe
                                                                                    seq (coe v36)
                                                                                    (coe
                                                                                       C_failure_394
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_38))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     C_failure_394 v26 -> coe v25
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    C_failure_394 v17 -> coe v16
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v13)
                C_failure_394 v8 -> coe v7
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe
             C_success_392 (coe MAlonzo.Code.Once.Type.C_Unit_48)
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_436 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
             (coe (0 :: Integer)) (coe d_freshCounter_442 (coe v0))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v2
        -> coe
             C_success_392 (coe MAlonzo.Code.Once.Type.C_Int_64)
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_436 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_int_350 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_442 (coe v0))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v2
        -> coe
             C_success_392 (coe MAlonzo.Code.Once.Type.C_Str_68)
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_436 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_str_356 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_442 (coe v0))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v2 v3
        -> let v4 = d_checkElab_1368 (coe v0) (coe v2) (coe v3) in
           coe
             (case coe v4 of
                C_success_416 v5 v6 v7 v8
                  -> coe C_success_392 (coe v3) (coe v5) (coe v6) (coe v7) (coe v8)
                C_failure_418 v5 -> coe C_failure_394 (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v2 v3 v4
        -> let v5
                 = coe du_asInt_1014 (coe d_inferElab_1362 (coe v0) (coe v3)) in
           coe
             (case coe v5 of
                C_isInt_1006 v6 v7 v8 v9
                  -> let v10
                           = coe du_asInt_1014 (coe d_inferElab_1362 (coe v0) (coe v4)) in
                     coe
                       (case coe v10 of
                          C_isInt_1006 v11 v12 v13 v14
                            -> coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe MAlonzo.Code.Once.TypeCheck.Raw.d_isArithmeticOp_90 (coe v2))
                                 (coe
                                    C_success_392 (coe MAlonzo.Code.Once.Type.C_Int_64)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v6)
                                       (coe v11))
                                    (coe du_mkArith_2524 v6 v11 v2 v7 v12)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v13))
                                    (coe v14))
                                 (coe
                                    C_success_392
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'43'__54
                                       (coe MAlonzo.Code.Once.Type.C_Unit_48)
                                       (coe MAlonzo.Code.Once.Type.C_Unit_48))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v6)
                                       (coe v11))
                                    (coe du_mkCmp_2532 v6 v11 v2 v7 v12)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v13))
                                    (coe v14))
                          C_notInt_1008 v11
                            -> coe
                                 C_failure_394
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_70
                                    (coe v11))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_notInt_1008 v6
                  -> coe
                       C_failure_394
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_68 (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v3
        -> let v4 = d_inferElab_1362 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                C_success_392 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               C_failure_394
                               (coe MAlonzo.Code.Once.TypeCheck.Error.C_NegationNotInt_34) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Once.Type.C_Int_64
                            -> coe
                                 C_success_392 (coe v5) (coe v6)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_414 v7) (coe v8)
                                 (coe v9)
                          _ -> coe v10)
                C_failure_394 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_1368 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
d_checkElab_1368 v0 v1 v2
  = let v3
          = let v3 = d_inferElab_1362 (coe v0) (coe v1) in
            coe
              (case coe v3 of
                 C_success_392 v4 v5 v6 v7 v8
                   -> let v9 = d__'8799'T__16 (coe v2) (coe v4) in
                      coe
                        (case coe v9 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                             -> if coe v10
                                  then coe
                                         seq (coe v11)
                                         (coe C_success_416 (coe v5) (coe v6) (coe v7) (coe v8))
                                  else coe
                                         seq (coe v11)
                                         (coe
                                            C_failure_418
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                               (coe v2) (coe v4)))
                           _ -> MAlonzo.RTE.mazUnreachableError)
                 C_failure_394 v4 -> coe C_failure_418 (coe v4)
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v4 v5
           -> let v6 = d_classifyAppHeadView_1152 (coe v4) in
              coe
                (case coe v6 of
                   C_ahv'45'id_1132
                     -> let v7 = d_inferElab_1362 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             C_success_392 v8 v9 v10 v11 v12
                               -> let v13
                                        = coe
                                            MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                            (coe
                                               MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                               (coe d_size_436 (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)) in
                                  coe
                                    (let v14
                                           = coe
                                               MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                               (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                  (coe d_size_436 (coe v0)))
                                               v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                  (coe d_debruijn_440 (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                     (coe v8) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v8))
                                                  (coe du_specId_496))
                                               v10 in
                                     coe
                                       (let v15 = addInt (coe (1 :: Integer)) (coe v11) in
                                        coe
                                          (let v16 = d__'8799'T__16 (coe v2) (coe v8) in
                                           coe
                                             (case coe v16 of
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                  -> if coe v17
                                                       then coe
                                                              seq (coe v18)
                                                              (coe
                                                                 C_success_416 (coe v13) (coe v14)
                                                                 (coe v15) (coe v12))
                                                       else coe
                                                              seq (coe v18)
                                                              (coe
                                                                 C_failure_418
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                    (coe v2) (coe v8)))
                                                _ -> MAlonzo.RTE.mazUnreachableError))))
                             C_failure_394 v8
                               -> case coe v7 of
                                    C_success_392 v9 v10 v11 v12 v13
                                      -> let v14 = d__'8799'T__16 (coe v2) (coe v9) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_success_416 (coe v10) (coe v11)
                                                               (coe v12) (coe v13))
                                                     else coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_failure_418
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v9 -> coe C_failure_418 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'fst_1134
                     -> let v7 = d_inferElab_1362 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             C_success_392 v8 v9 v10 v11 v12
                               -> case coe v8 of
                                    MAlonzo.Code.Once.Type.C__'42'__52 v13 v14
                                      -> let v15
                                               = coe
                                                   MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                      (coe d_size_436 (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)) in
                                         coe
                                           (let v16
                                                  = coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                      (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                         (coe d_size_436 (coe v0)))
                                                      v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                         (coe d_debruijn_440 (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                            (coe v8)
                                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                            (coe v13))
                                                         (coe du_specFst_504 (coe v14)))
                                                      v10 in
                                            coe
                                              (let v17 = addInt (coe (1 :: Integer)) (coe v11) in
                                               coe
                                                 (let v18 = d__'8799'T__16 (coe v2) (coe v13) in
                                                  coe
                                                    (case coe v18 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                         -> if coe v19
                                                              then coe
                                                                     seq (coe v20)
                                                                     (coe
                                                                        C_success_416 (coe v15)
                                                                        (coe v16) (coe v17)
                                                                        (coe v12))
                                                              else coe
                                                                     seq (coe v20)
                                                                     (coe
                                                                        C_failure_418
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                           (coe v2) (coe v13)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError))))
                                    _ -> let v13
                                               = coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_30 in
                                         coe (coe C_failure_418 (coe v13))
                             C_failure_394 v8
                               -> case coe v7 of
                                    C_success_392 v9 v10 v11 v12 v13
                                      -> let v14 = d__'8799'T__16 (coe v2) (coe v9) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_success_416 (coe v10) (coe v11)
                                                               (coe v12) (coe v13))
                                                     else coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_failure_418
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v9 -> coe C_failure_418 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'snd_1136
                     -> let v7 = d_inferElab_1362 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             C_success_392 v8 v9 v10 v11 v12
                               -> case coe v8 of
                                    MAlonzo.Code.Once.Type.C__'42'__52 v13 v14
                                      -> let v15
                                               = coe
                                                   MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                      (coe d_size_436 (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)) in
                                         coe
                                           (let v16
                                                  = coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                      (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                         (coe d_size_436 (coe v0)))
                                                      v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                         (coe d_debruijn_440 (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                            (coe v8)
                                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                            (coe v14))
                                                         (coe du_specSnd_514 (coe v13)))
                                                      v10 in
                                            coe
                                              (let v17 = addInt (coe (1 :: Integer)) (coe v11) in
                                               coe
                                                 (let v18 = d__'8799'T__16 (coe v2) (coe v14) in
                                                  coe
                                                    (case coe v18 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                         -> if coe v19
                                                              then coe
                                                                     seq (coe v20)
                                                                     (coe
                                                                        C_success_416 (coe v15)
                                                                        (coe v16) (coe v17)
                                                                        (coe v12))
                                                              else coe
                                                                     seq (coe v20)
                                                                     (coe
                                                                        C_failure_418
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                           (coe v2) (coe v14)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError))))
                                    _ -> let v13
                                               = coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_32 in
                                         coe (coe C_failure_418 (coe v13))
                             C_failure_394 v8
                               -> case coe v7 of
                                    C_success_392 v9 v10 v11 v12 v13
                                      -> let v14 = d__'8799'T__16 (coe v2) (coe v9) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_success_416 (coe v10) (coe v11)
                                                               (coe v12) (coe v13))
                                                     else coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_failure_418
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v9 -> coe C_failure_418 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'terminal_1138
                     -> let v7 = d_inferElab_1362 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             C_success_392 v8 v9 v10 v11 v12
                               -> let v13 = coe MAlonzo.Code.Once.Type.C_Unit_48 in
                                  coe
                                    (let v14
                                           = coe
                                               MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                  (coe d_size_436 (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe v9)) in
                                     coe
                                       (let v15
                                              = coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                  (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                     (coe d_size_436 (coe v0)))
                                                  v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                     (coe d_debruijn_440 (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                        (coe v8)
                                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                        (coe MAlonzo.Code.Once.Type.C_Unit_48))
                                                     (coe du_specTerminal_558))
                                                  v10 in
                                        coe
                                          (let v16 = addInt (coe (1 :: Integer)) (coe v11) in
                                           coe
                                             (let v17 = d__'8799'T__16 (coe v2) (coe v13) in
                                              coe
                                                (case coe v17 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                     -> if coe v18
                                                          then coe
                                                                 seq (coe v19)
                                                                 (coe
                                                                    C_success_416 (coe v14)
                                                                    (coe v15) (coe v16) (coe v12))
                                                          else coe
                                                                 seq (coe v19)
                                                                 (coe
                                                                    C_failure_418
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                       (coe v2) (coe v13)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError)))))
                             C_failure_394 v8
                               -> case coe v7 of
                                    C_success_392 v9 v10 v11 v12 v13
                                      -> let v14 = d__'8799'T__16 (coe v2) (coe v9) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_success_416 (coe v10) (coe v11)
                                                               (coe v12) (coe v13))
                                                     else coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_failure_418
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v9 -> coe C_failure_418 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'inl_1140
                     -> case coe v2 of
                          MAlonzo.Code.Once.Type.C_Unit_48
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Void_50
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C__'42'__52 v7 v8
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C__'43'__54 v7 v8
                            -> let v9 = d_checkElab_1368 (coe v0) (coe v5) (coe v7) in
                               coe
                                 (case coe v9 of
                                    C_success_416 v10 v11 v12 v13
                                      -> coe
                                           C_success_416
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_436 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_436 (coe v0)))
                                              v10 v7 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                 (coe d_debruijn_440 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                    (coe v7) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v2))
                                                 (coe du_specInl_524))
                                              v11)
                                           (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                                    C_failure_418 v10 -> coe v9
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v7 v8 v9
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Eff_58 v7 v8
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_μ'45'type_60 v7
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_ν'45'type_62 v7
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Int_64
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Float_66
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Str_68
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Buffer_70
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'inr_1142
                     -> case coe v2 of
                          MAlonzo.Code.Once.Type.C_Unit_48
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Void_50
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C__'42'__52 v7 v8
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C__'43'__54 v7 v8
                            -> let v9 = d_checkElab_1368 (coe v0) (coe v5) (coe v8) in
                               coe
                                 (case coe v9 of
                                    C_success_416 v10 v11 v12 v13
                                      -> coe
                                           C_success_416
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_436 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_436 (coe v0)))
                                              v10 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                 (coe d_debruijn_440 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                    (coe v8) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v2))
                                                 (coe du_specInr_534))
                                              v11)
                                           (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                                    C_failure_418 v10 -> coe v9
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v7 v8 v9
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Eff_58 v7 v8
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_μ'45'type_60 v7
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_ν'45'type_62 v7
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Int_64
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Float_66
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Str_68
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Buffer_70
                            -> coe
                                 C_failure_418
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'initial_1144
                     -> let v7
                              = d_checkElab_1368
                                  (coe v0) (coe v5) (coe MAlonzo.Code.Once.Type.C_Void_50) in
                        coe
                          (case coe v7 of
                             C_success_416 v8 v9 v10 v11
                               -> coe
                                    C_success_416
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                          (coe d_size_436 (coe v0)))
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                       (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                          (coe d_size_436 (coe v0)))
                                       v8 (coe MAlonzo.Code.Once.Type.C_Void_50)
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                          (coe d_debruijn_440 (coe v0))
                                          (coe
                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                             (coe MAlonzo.Code.Once.Type.C_Void_50)
                                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                                          (coe du_specInitial_564))
                                       v9)
                                    (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11)
                             C_failure_418 v8 -> coe v7
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'other_1148
                     -> let v8
                              = coe du_asFun_940 (coe d_inferElab_1362 (coe v0) (coe v4)) in
                        coe
                          (case coe v8 of
                             C_isFun_924 v9 v10 v11 v12 v13 v14 v15
                               -> let v16 = d_inferElab_1362 (coe v0) (coe v5) in
                                  coe
                                    (case coe v16 of
                                       C_success_392 v17 v18 v19 v20 v21
                                         -> let v22 = d__'8799'T__16 (coe v9) (coe v17) in
                                            coe
                                              (case coe v22 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                   -> if coe v23
                                                        then let v25
                                                                   = seq
                                                                       (coe v24)
                                                                       (coe
                                                                          C_success_392 (coe v11)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                             (coe v12)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                (coe v10)
                                                                                (coe v18)))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                             v12 v18 v17 v10 v13
                                                                             v19)
                                                                          (coe
                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                             (coe v14) (coe v20))
                                                                          (coe v21)) in
                                                             coe
                                                               (case coe v25 of
                                                                  C_success_392 v26 v27 v28 v29 v30
                                                                    -> let v31
                                                                             = d__'8799'T__16
                                                                                 (coe v2)
                                                                                 (coe v26) in
                                                                       coe
                                                                         (case coe v31 of
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v32 v33
                                                                              -> if coe v32
                                                                                   then coe
                                                                                          seq
                                                                                          (coe v33)
                                                                                          (coe
                                                                                             C_success_416
                                                                                             (coe
                                                                                                v27)
                                                                                             (coe
                                                                                                v28)
                                                                                             (coe
                                                                                                v29)
                                                                                             (coe
                                                                                                v30))
                                                                                   else coe
                                                                                          seq
                                                                                          (coe v33)
                                                                                          (coe
                                                                                             C_failure_418
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                                                (coe
                                                                                                   v2)
                                                                                                (coe
                                                                                                   v26)))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  C_failure_394 v26
                                                                    -> coe C_failure_418 (coe v26)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        else (let v25
                                                                    = seq
                                                                        (coe v24)
                                                                        (coe
                                                                           C_failure_394
                                                                           (coe
                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_ApplicationTypeMismatch_44
                                                                              (coe v9)
                                                                              (coe v17))) in
                                                              coe
                                                                (case coe v25 of
                                                                   C_success_392 v26 v27 v28 v29 v30
                                                                     -> let v31
                                                                              = d__'8799'T__16
                                                                                  (coe v2)
                                                                                  (coe v26) in
                                                                        coe
                                                                          (case coe v31 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v32 v33
                                                                               -> if coe v32
                                                                                    then coe
                                                                                           seq
                                                                                           (coe v33)
                                                                                           (coe
                                                                                              C_success_416
                                                                                              (coe
                                                                                                 v27)
                                                                                              (coe
                                                                                                 v28)
                                                                                              (coe
                                                                                                 v29)
                                                                                              (coe
                                                                                                 v30))
                                                                                    else coe
                                                                                           seq
                                                                                           (coe v33)
                                                                                           (coe
                                                                                              C_failure_418
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                                                 (coe
                                                                                                    v2)
                                                                                                 (coe
                                                                                                    v26)))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   C_failure_394 v26
                                                                     -> coe C_failure_418 (coe v26)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       C_failure_394 v17
                                         -> case coe v16 of
                                              C_success_392 v18 v19 v20 v21 v22
                                                -> let v23 = d__'8799'T__16 (coe v2) (coe v18) in
                                                   coe
                                                     (case coe v23 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                          -> if coe v24
                                                               then coe
                                                                      seq (coe v25)
                                                                      (coe
                                                                         C_success_416 (coe v19)
                                                                         (coe v20) (coe v21)
                                                                         (coe v22))
                                                               else coe
                                                                      seq (coe v25)
                                                                      (coe
                                                                         C_failure_418
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                            (coe v2) (coe v18)))
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              C_failure_394 v18 -> coe C_failure_418 (coe v18)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             C_isEff_932 v9 v10 v11 v12 v13 v14
                               -> let v15 = d_inferElab_1362 (coe v0) (coe v5) in
                                  coe
                                    (case coe v15 of
                                       C_success_392 v16 v17 v18 v19 v20
                                         -> let v21 = d__'8799'T__16 (coe v9) (coe v16) in
                                            coe
                                              (case coe v21 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                   -> if coe v22
                                                        then let v24
                                                                   = seq
                                                                       (coe v23)
                                                                       (coe
                                                                          C_success_392
                                                                          (coe
                                                                             MAlonzo.Code.Once.Type.C_Eff_58
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.C_Unit_48)
                                                                             (coe v10))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                             (coe v11) (coe v17))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Surface.Syntax.C_effApp_228
                                                                             v11 v17 v16 v12 v18)
                                                                          (coe
                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                             (coe v13) (coe v19))
                                                                          (coe v20)) in
                                                             coe
                                                               (case coe v24 of
                                                                  C_success_392 v25 v26 v27 v28 v29
                                                                    -> let v30
                                                                             = d__'8799'T__16
                                                                                 (coe v2)
                                                                                 (coe v25) in
                                                                       coe
                                                                         (case coe v30 of
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                              -> if coe v31
                                                                                   then coe
                                                                                          seq
                                                                                          (coe v32)
                                                                                          (coe
                                                                                             C_success_416
                                                                                             (coe
                                                                                                v26)
                                                                                             (coe
                                                                                                v27)
                                                                                             (coe
                                                                                                v28)
                                                                                             (coe
                                                                                                v29))
                                                                                   else coe
                                                                                          seq
                                                                                          (coe v32)
                                                                                          (coe
                                                                                             C_failure_418
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                                                (coe
                                                                                                   v2)
                                                                                                (coe
                                                                                                   v25)))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  C_failure_394 v25
                                                                    -> coe C_failure_418 (coe v25)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        else (let v24
                                                                    = seq
                                                                        (coe v23)
                                                                        (coe
                                                                           C_failure_394
                                                                           (coe
                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_ApplicationTypeMismatch_44
                                                                              (coe v9)
                                                                              (coe v16))) in
                                                              coe
                                                                (case coe v24 of
                                                                   C_success_392 v25 v26 v27 v28 v29
                                                                     -> let v30
                                                                              = d__'8799'T__16
                                                                                  (coe v2)
                                                                                  (coe v25) in
                                                                        coe
                                                                          (case coe v30 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                               -> if coe v31
                                                                                    then coe
                                                                                           seq
                                                                                           (coe v32)
                                                                                           (coe
                                                                                              C_success_416
                                                                                              (coe
                                                                                                 v26)
                                                                                              (coe
                                                                                                 v27)
                                                                                              (coe
                                                                                                 v28)
                                                                                              (coe
                                                                                                 v29))
                                                                                    else coe
                                                                                           seq
                                                                                           (coe v32)
                                                                                           (coe
                                                                                              C_failure_418
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                                                 (coe
                                                                                                    v2)
                                                                                                 (coe
                                                                                                    v25)))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   C_failure_394 v25
                                                                     -> coe C_failure_418 (coe v25)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       C_failure_394 v16
                                         -> case coe v15 of
                                              C_success_392 v17 v18 v19 v20 v21
                                                -> let v22 = d__'8799'T__16 (coe v2) (coe v17) in
                                                   coe
                                                     (case coe v22 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                          -> if coe v23
                                                               then coe
                                                                      seq (coe v24)
                                                                      (coe
                                                                         C_success_416 (coe v18)
                                                                         (coe v19) (coe v20)
                                                                         (coe v21))
                                                               else coe
                                                                      seq (coe v24)
                                                                      (coe
                                                                         C_failure_418
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_50
                                                                            (coe v2) (coe v17)))
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              C_failure_394 v17 -> coe C_failure_418 (coe v17)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             C_notFun_934 v9 -> coe C_failure_418 (coe v9)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v4 v5
           -> let v6
                    = coe
                        C_failure_418
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_LambdaRequiresFunctionType_18) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v7 v8 v9
                     -> let v10
                              = d_checkElab_1368
                                  (coe d_extendNamedCtx_462 (coe v0) (coe v4) (coe v7)) (coe v5)
                                  (coe v9) in
                        coe
                          (case coe v10 of
                             C_success_416 v11 v12 v13 v14
                               -> case coe v11 of
                                    MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v16 v17
                                      -> let v18 = d_decideLeq_1052 (coe v16) (coe v8) in
                                         coe
                                           (case coe v18 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                -> coe
                                                     C_success_416 (coe v17)
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_lam_198
                                                        v16 v12)
                                                     (coe addInt (coe (1 :: Integer)) (coe v13))
                                                     (coe v14)
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe
                                                     C_failure_418
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_62
                                                        (coe v4) (coe v8) (coe v16))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             C_failure_418 v11 -> coe v10
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v6)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate._.mkArith
d_mkArith_2524 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_mkArith_2524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               ~v12 v13 v14 v15
  = du_mkArith_2524 v13 v14 v15
du_mkArith_2524 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_mkArith_2524 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.Surface.Syntax.C_add_366 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_add_366 (coe v0) (coe v1)
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_sub_376 (coe v0) (coe v1)
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_mul_386 (coe v0) (coe v1)
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_div_396 (coe v0) (coe v1)
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
           -> coe
                MAlonzo.Code.Once.Surface.Syntax.C_mod''_406 (coe v0) (coe v1)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate._.mkCmp
d_mkCmp_2532 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_mkCmp_2532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             v13 v14 v15
  = du_mkCmp_2532 v13 v14 v15
du_mkCmp_2532 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_mkCmp_2532 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.Surface.Syntax.C_lt_424 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_lt_424 (coe v0) (coe v1)
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_le_434 (coe v0) (coe v1)
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_gt_444 (coe v0) (coe v1)
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_ge_454 (coe v0) (coe v1)
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_eq_464 (coe v0) (coe v1)
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_ne_474 (coe v0) (coe v1)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RInt
d_checkElab'45'fallback'45'RInt_3498 ::
  T_NamedCtx_424 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RInt_3498 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_int_350 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_442 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RStringLit
d_checkElab'45'fallback'45'RStringLit_3528 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RStringLit_3528 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_str_356 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_442 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RUnit
d_checkElab'45'fallback'45'RUnit_3556 ::
  T_NamedCtx_424 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnit_3556 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_442 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RQualified
d_checkElab'45'fallback'45'RQualified_3592 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RQualified_3592 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
                                           v7 ~v8
  = du_checkElab'45'fallback'45'RQualified_3592 v3 v5 v6 v7
du_checkElab'45'fallback'45'RQualified_3592 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RQualified_3592 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RAnnot
d_checkElab'45'fallback'45'RAnnot_3648 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RAnnot_3648 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
  = du_checkElab'45'fallback'45'RAnnot_3648 v2 v4 v5 v6
du_checkElab'45'fallback'45'RAnnot_3648 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RAnnot_3648 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RPair
d_checkElab'45'fallback'45'RPair_3700 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RPair_3700 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
                                      ~v8
  = du_checkElab'45'fallback'45'RPair_3700 v3 v5 v6 v7
du_checkElab'45'fallback'45'RPair_3700 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RPair_3700 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RLet
d_checkElab'45'fallback'45'RLet_3760 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RLet_3760 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7
                                     v8 ~v9
  = du_checkElab'45'fallback'45'RLet_3760 v4 v6 v7 v8
du_checkElab'45'fallback'45'RLet_3760 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RLet_3760 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RDestruct
d_checkElab'45'fallback'45'RDestruct_3830 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RDestruct_3830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                          v6 ~v7 v8 v9 v10 ~v11
  = du_checkElab'45'fallback'45'RDestruct_3830 v6 v8 v9 v10
du_checkElab'45'fallback'45'RDestruct_3830 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RDestruct_3830 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RUnaryOp
d_checkElab'45'fallback'45'RUnaryOp_3906 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_UnaryOp_30 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp_3906 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
                                         v7 ~v8
  = du_checkElab'45'fallback'45'RUnaryOp_3906 v3 v5 v6 v7
du_checkElab'45'fallback'45'RUnaryOp_3906 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp_3906 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-unit
d_checkElab'45'fallback'45'RVar'45'unit_3950 ::
  T_NamedCtx_424 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'unit_3950 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_442 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-id
d_checkElab'45'fallback'45'RApp'45'id_3984 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id_3984 ~v0 ~v1 v2 ~v3 v4 v5 v6
                                           ~v7
  = du_checkElab'45'fallback'45'RApp'45'id_3984 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'id_3984 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id_3984 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-fst
d_checkElab'45'fallback'45'RApp'45'fst_4034 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst_4034 ~v0 ~v1 v2 ~v3 v4 v5 v6
                                            ~v7
  = du_checkElab'45'fallback'45'RApp'45'fst_4034 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'fst_4034 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst_4034 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-snd
d_checkElab'45'fallback'45'RApp'45'snd_4084 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd_4084 ~v0 ~v1 v2 ~v3 v4 v5 v6
                                            ~v7
  = du_checkElab'45'fallback'45'RApp'45'snd_4084 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'snd_4084 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd_4084 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-generic
d_checkElab'45'fallback'45'RApp'45'generic_4136 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic_4136 ~v0 ~v1 ~v2 v3 ~v4
                                                v5 v6 v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'generic_4136 v3 v5 v6 v7
du_checkElab'45'fallback'45'RApp'45'generic_4136 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic_4136 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-terminal
d_checkElab'45'fallback'45'RApp'45'terminal_4206 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'terminal_4206 ~v0 ~v1 v2 ~v3 v4
                                                 v5 v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'terminal_4206 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'terminal_4206 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'terminal_4206 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RBinOp
d_checkElab'45'fallback'45'RBinOp_4260 ::
  T_NamedCtx_424 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RBinOp_4260 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7
                                       v8 ~v9
  = du_checkElab'45'fallback'45'RBinOp_4260 v4 v6 v7 v8
du_checkElab'45'fallback'45'RBinOp_4260 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RBinOp_4260 v0 v1 v2 v3
  = let v4 = d__'8799'T__16 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExprTyped
d_compileExprTyped_4304 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_12
d_compileExprTyped_4304 v0 v1
  = let v2
          = d_checkElab_1368 (coe d_emptyCtx_448) (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_success_416 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_114
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v1)
                   (coe v4))
         C_failure_418 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExpr
d_compileExpr_4328 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_4328 v0
  = let v1 = d_inferElab_1362 (coe d_emptyCtx_448) (coe v0) in
    coe
      (case coe v1 of
         C_success_392 v2 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_114
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v2)
                      (coe v4)))
         C_failure_394 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
