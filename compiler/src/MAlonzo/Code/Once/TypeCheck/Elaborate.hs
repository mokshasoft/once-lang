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
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
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
-- Once.TypeCheck.Elaborate.PolyCtx
d_PolyCtx_424 :: ()
d_PolyCtx_424 = erased
-- Once.TypeCheck.Elaborate.emptyPolyCtx
d_emptyPolyCtx_426 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyPolyCtx_426
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Elaborate.lookupPoly
d_lookupPoly_428 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly_428 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
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
                                 else coe seq (coe v8) (coe d_lookupPoly_428 (coe v3) (coe v1))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.removePoly
d_removePoly_464 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_removePoly_464 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe v0)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe seq (coe v8) (coe v3)
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                                           (coe d_removePoly_464 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx
d_NamedCtx_500 = ()
data T_NamedCtx_500
  = C_mkCtx_526 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 Integer
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Elaborate.NamedCtx.size
d_size_514 :: T_NamedCtx_500 -> Integer
d_size_514 v0
  = case coe v0 of
      C_mkCtx_526 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.named
d_named_516 ::
  T_NamedCtx_500 -> [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_516 v0
  = case coe v0 of
      C_mkCtx_526 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.debruijn
d_debruijn_518 ::
  T_NamedCtx_500 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_518 v0
  = case coe v0 of
      C_mkCtx_526 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.freshCounter
d_freshCounter_520 :: T_NamedCtx_500 -> Integer
d_freshCounter_520 v0
  = case coe v0 of
      C_mkCtx_526 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.imports
d_imports_522 ::
  T_NamedCtx_500 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_522 v0
  = case coe v0 of
      C_mkCtx_526 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.polys
d_polys_524 ::
  T_NamedCtx_500 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_524 v0
  = case coe v0 of
      C_mkCtx_526 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.emptyCtx
d_emptyCtx_528 :: T_NamedCtx_500
d_emptyCtx_528
  = coe
      C_mkCtx_526 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe d_emptyImports_422)
      (coe d_emptyPolyCtx_426)
-- Once.TypeCheck.Elaborate.ctxWithImports
d_ctxWithImports_530 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_500
d_ctxWithImports_530 v0
  = coe
      C_mkCtx_526 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe d_emptyPolyCtx_426)
-- Once.TypeCheck.Elaborate.ctxWithImportsAndPolys
d_ctxWithImportsAndPolys_534 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_500
d_ctxWithImportsAndPolys_534 v0 v1
  = coe
      C_mkCtx_526 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe v1)
-- Once.TypeCheck.Elaborate.ctxWithImportsAndSelf
d_ctxWithImportsAndSelf_540 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_NamedCtx_500
d_ctxWithImportsAndSelf_540 v0 v1 v2
  = coe
      d_ctxWithImports_530
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
         (coe v0))
-- Once.TypeCheck.Elaborate.ctxWithImportsAndSelfAndPolys
d_ctxWithImportsAndSelfAndPolys_548 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_NamedCtx_500
d_ctxWithImportsAndSelfAndPolys_548 v0 v1 v2 v3
  = coe
      d_ctxWithImportsAndPolys_534
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
         (coe v0))
      (coe v1)
-- Once.TypeCheck.Elaborate.extendNamedCtx
d_extendNamedCtx_558 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_NamedCtx_500
d_extendNamedCtx_558 v0 v1 v2
  = case coe v0 of
      C_mkCtx_526 v3 v4 v5 v6 v7 v8
        -> coe
             C_mkCtx_526 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v5) (coe v2))
             (coe v6) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.bumpFresh
d_bumpFresh_576 :: T_NamedCtx_500 -> T_NamedCtx_500
d_bumpFresh_576 v0
  = case coe v0 of
      C_mkCtx_526 v1 v2 v3 v4 v5 v6
        -> coe
             C_mkCtx_526 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.freshTVar
d_freshTVar_590 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_590 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Elaborate.specId
d_specId_596 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specId_596 ~v0 = du_specId_596
du_specId_596 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specId_596
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_var_182
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.TypeCheck.Elaborate.specFst
d_specFst_604 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specFst_604 ~v0 v1 = du_specFst_604 v1
du_specFst_604 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specFst_604 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v0
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_614 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specSnd_614 v0 ~v1 = du_specSnd_614 v0
du_specSnd_614 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specSnd_614 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v0
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specInl
d_specInl_624 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specInl_624 ~v0 ~v1 = du_specInl_624
du_specInl_624 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specInl_624
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_inl''_278
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specInr
d_specInr_634 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specInr_634 ~v0 ~v1 = du_specInr_634
du_specInr_634 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specInr_634
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_inr''_290
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_640 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specUnitGen_640 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318
-- Once.TypeCheck.Elaborate.specPair
d_specPair_648 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specPair_648 v0 ~v1 ~v2 = du_specPair_648 v0
du_specPair_648 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specPair_648 v0
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
d_specTerminal_658 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specTerminal_658 ~v0 = du_specTerminal_658
du_specTerminal_658 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specTerminal_658
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_Zero_6)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_664 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specInitial_664 ~v0 = du_specInitial_664
du_specInitial_664 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specInitial_664
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_absurd_328
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_674 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specCurry_674 v0 v1 ~v2 = du_specCurry_674 v0 v1
du_specCurry_674 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specCurry_674 v0 v1
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
d_specApply_686 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specApply_686 v0 v1
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
d_specCompose_698 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specCompose_698 v0 v1 ~v2 = du_specCompose_698 v0 v1
du_specCompose_698 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specCompose_698 v0 v1
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
d_specArr_710 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specArr_710 ~v0 ~v1 = du_specArr_710
du_specArr_710 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specArr_710
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_arr''_486
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.lookupImport
d_lookupImport_716 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_38
d_lookupImport_716 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupImport_716 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_746 = ()
data T_AppSpine_746
  = C_mkSpine_756 MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_752 ::
  T_AppSpine_746 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_head_752 v0
  = case coe v0 of
      C_mkSpine_756 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_754 ::
  T_AppSpine_746 -> [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
d_args_754 v0
  = case coe v0 of
      C_mkSpine_756 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_758 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppSpine_746
d_spineOf_758 v0
  = coe
      du_go_766 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_766 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_746
d_go_766 ~v0 v1 v2 = du_go_766 v1 v2
du_go_766 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_746
du_go_766 v0 v1
  = let v2 = coe C_mkSpine_756 (coe v0) (coe v1) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v3 v4
           -> coe
                du_go_766 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v1))
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_778 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_778 v0
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
d_lookupLocal_786 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal_786 v0 v1
  = case coe v0 of
      C_mkCtx_526 v2 v3 v4 v5 v6 v7
        -> coe du_go_808 (coe v1) (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_808 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_808 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_go_808 v6 v7 v8 v9
du_go_808 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_808 v0 v1 v2 v3
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
                                                   du_go_808 (coe v0) (coe v10) (coe v5) (coe v7) in
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
d_findLocalVarUsage_876 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findLocalVarUsage_876 v0 v1
  = case coe v0 of
      C_mkCtx_526 v2 v3 v4 v5 v6 v7
        -> coe du_go_892 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_892 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_892 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 = du_go_892 v6 v8 v9
du_go_892 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_892 v0 v1 v2
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
                                     (let v12 = coe du_go_892 (coe v0) (coe v4) (coe v6) in
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
d_matchInferResult_962 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_InferElabResult_378 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
d_matchInferResult_962 ~v0 ~v1 v2 v3
  = du_matchInferResult_962 v2 v3
du_matchInferResult_962 ::
  T_InferElabResult_378 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
du_matchInferResult_962 v0 v1
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
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v1)
                                    (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_394 v2 -> coe C_failure_418 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.FunProjection
d_FunProjection_1010 a0 a1 = ()
data T_FunProjection_1010
  = C_isFun_1024 MAlonzo.Code.Once.Type.T_Type_38
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Type_38
                 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_isEff_1032 MAlonzo.Code.Once.Type.T_Type_38
                 MAlonzo.Code.Once.Type.T_Type_38
                 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_notFun_1034 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asFun
d_asFun_1040 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_InferElabResult_378 -> T_FunProjection_1010
d_asFun_1040 ~v0 ~v1 v2 = du_asFun_1040 v2
du_asFun_1040 :: T_InferElabResult_378 -> T_FunProjection_1010
du_asFun_1040 v0
  = case coe v0 of
      C_success_392 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__52 v6 v7
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__54 v6 v7
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v6 v7 v8
               -> coe
                    C_isFun_1024 (coe v6) (coe v7) (coe v8) (coe v2) (coe v3) (coe v4)
                    (coe v5)
             MAlonzo.Code.Once.Type.C_Eff_58 v6 v7
               -> coe
                    C_isEff_1032 (coe v6) (coe v7) (coe v2) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v6
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v6
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    C_notFun_1034
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_394 v1 -> coe C_notFun_1034 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_1098 a0 a1 = ()
data T_IntProjection_1098
  = C_isInt_1106 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_notInt_1108 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1114 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_InferElabResult_378 -> T_IntProjection_1098
d_asInt_1114 ~v0 ~v1 v2 = du_asInt_1114 v2
du_asInt_1114 :: T_InferElabResult_378 -> T_IntProjection_1098
du_asInt_1114 v0
  = case coe v0 of
      C_success_392 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_48
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Void_50
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__52 v6 v7
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__54 v6 v7
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v6 v7 v8
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Eff_58 v6 v7
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v6
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v6
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Int_64
               -> coe C_isInt_1106 (coe v2) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_Float_66
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Str_68
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_70
               -> coe
                    C_notInt_1108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_64) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_394 v1 -> coe C_notInt_1108 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.decideLeq
d_decideLeq_1152 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1152 v0 v1
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
d_PolyBuiltinApp_1154 = ()
data T_PolyBuiltinApp_1154
  = C_pba'45'id_1156 | C_pba'45'fst_1158 | C_pba'45'snd_1160 |
    C_pba'45'terminal_1162 | C_pba'45'inl_1164 | C_pba'45'inr_1166 |
    C_pba'45'initial_1168 | C_pba'45'arr_1170 |
    C_pba'45'pair'45'applied_1172 | C_pba'45'compose'45'applied_1174 |
    C_pba'45'curry_1176 | C_pba'45'apply_1178
-- Once.TypeCheck.Elaborate.classifyAppHead
d_classifyAppHead_1180 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe T_PolyBuiltinApp_1154
d_classifyAppHead_1180 v0
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
                                    (coe C_pba'45'id_1156))
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
                                                        (coe C_pba'45'fst_1158))
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
                                                                            (coe C_pba'45'snd_1160))
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
                                                                                                   C_pba'45'terminal_1162))
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
                                                                                                                       C_pba'45'inl_1164))
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
                                                                                                                                           C_pba'45'inr_1166))
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
                                                                                                                                                               C_pba'45'initial_1168))
                                                                                                                                                  else coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v23)
                                                                                                                                                         (let v24
                                                                                                                                                                = coe
                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                    erased
                                                                                                                                                                    (\ v24 ->
                                                                                                                                                                       coe
                                                                                                                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                         (coe
                                                                                                                                                                            v2))
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                       (coe
                                                                                                                                                                          v2)
                                                                                                                                                                       (coe
                                                                                                                                                                          ("arr"
                                                                                                                                                                           ::
                                                                                                                                                                           Data.Text.Text))) in
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
                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                (coe
                                                                                                                                                                                   C_pba'45'arr_1170))
                                                                                                                                                                      else coe
                                                                                                                                                                             seq
                                                                                                                                                                             (coe
                                                                                                                                                                                v26)
                                                                                                                                                                             (let v27
                                                                                                                                                                                    = coe
                                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                        erased
                                                                                                                                                                                        (\ v27 ->
                                                                                                                                                                                           coe
                                                                                                                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                             (coe
                                                                                                                                                                                                v2))
                                                                                                                                                                                        (coe
                                                                                                                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                           (coe
                                                                                                                                                                                              v2)
                                                                                                                                                                                           (coe
                                                                                                                                                                                              ("curry"
                                                                                                                                                                                               ::
                                                                                                                                                                                               Data.Text.Text))) in
                                                                                                                                                                              coe
                                                                                                                                                                                (case coe
                                                                                                                                                                                        v27 of
                                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                                                                                                                                                                                     -> if coe
                                                                                                                                                                                             v28
                                                                                                                                                                                          then coe
                                                                                                                                                                                                 seq
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    v29)
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                    (coe
                                                                                                                                                                                                       C_pba'45'curry_1176))
                                                                                                                                                                                          else coe
                                                                                                                                                                                                 seq
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    v29)
                                                                                                                                                                                                 (let v30
                                                                                                                                                                                                        = coe
                                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                            erased
                                                                                                                                                                                                            (\ v30 ->
                                                                                                                                                                                                               coe
                                                                                                                                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    v2))
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v2)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  ("apply"
                                                                                                                                                                                                                   ::
                                                                                                                                                                                                                   Data.Text.Text))) in
                                                                                                                                                                                                  coe
                                                                                                                                                                                                    (case coe
                                                                                                                                                                                                            v30 of
                                                                                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                                                                                                                         -> if coe
                                                                                                                                                                                                                 v31
                                                                                                                                                                                                              then coe
                                                                                                                                                                                                                     seq
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        v32)
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                           C_pba'45'apply_1178))
                                                                                                                                                                                                              else coe
                                                                                                                                                                                                                     seq
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        v32)
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v2 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v5
                     -> let v6
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v6 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v5))
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v5)
                                     (coe ("pair" :: Data.Text.Text))) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe
                                           seq (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                              (coe C_pba'45'pair'45'applied_1172))
                                    else coe
                                           seq (coe v8)
                                           (let v9
                                                  = coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                      erased
                                                      (\ v9 ->
                                                         coe
                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                           (coe v5))
                                                      (coe
                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                         (coe v5)
                                                         (coe ("compose" :: Data.Text.Text))) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                   -> if coe v10
                                                        then coe
                                                               seq (coe v11)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                  (coe
                                                                     C_pba'45'compose'45'applied_1174))
                                                        else coe
                                                               seq (coe v11)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v4)
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.AppHeadView
d_AppHeadView_1282 a0 = ()
data T_AppHeadView_1282
  = C_ahv'45'id_1284 | C_ahv'45'fst_1286 | C_ahv'45'snd_1288 |
    C_ahv'45'terminal_1290 | C_ahv'45'inl_1292 | C_ahv'45'inr_1294 |
    C_ahv'45'initial_1296 | C_ahv'45'arr_1298 | C_ahv'45'curry_1300 |
    C_ahv'45'apply_1302 | C_ahv'45'pair'45'applied_1306 |
    C_ahv'45'compose'45'applied_1310 | C_ahv'45'other_1314
-- Once.TypeCheck.Elaborate.classifyAppHeadView
d_classifyAppHeadView_1318 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppHeadView_1282
d_classifyAppHeadView_1318 v0
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
                       then coe seq (coe v4) (coe C_ahv'45'id_1284)
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
                                           then coe seq (coe v7) (coe C_ahv'45'fst_1286)
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
                                                                      (coe C_ahv'45'snd_1288)
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
                                                                                             C_ahv'45'terminal_1290)
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
                                                                                                                 C_ahv'45'inl_1292)
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
                                                                                                                                     C_ahv'45'inr_1294)
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
                                                                                                                                                         C_ahv'45'initial_1296)
                                                                                                                                               else coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v22)
                                                                                                                                                      (let v23
                                                                                                                                                             = coe
                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                 erased
                                                                                                                                                                 (\ v23 ->
                                                                                                                                                                    coe
                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                      (coe
                                                                                                                                                                         v1))
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                    (coe
                                                                                                                                                                       v1)
                                                                                                                                                                    (coe
                                                                                                                                                                       ("arr"
                                                                                                                                                                        ::
                                                                                                                                                                        Data.Text.Text))) in
                                                                                                                                                       coe
                                                                                                                                                         (case coe
                                                                                                                                                                 v23 of
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                                                                              -> if coe
                                                                                                                                                                      v24
                                                                                                                                                                   then coe
                                                                                                                                                                          seq
                                                                                                                                                                          (coe
                                                                                                                                                                             v25)
                                                                                                                                                                          (coe
                                                                                                                                                                             C_ahv'45'arr_1298)
                                                                                                                                                                   else coe
                                                                                                                                                                          seq
                                                                                                                                                                          (coe
                                                                                                                                                                             v25)
                                                                                                                                                                          (let v26
                                                                                                                                                                                 = coe
                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                     erased
                                                                                                                                                                                     (\ v26 ->
                                                                                                                                                                                        coe
                                                                                                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                          (coe
                                                                                                                                                                                             v1))
                                                                                                                                                                                     (coe
                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                        (coe
                                                                                                                                                                                           v1)
                                                                                                                                                                                        (coe
                                                                                                                                                                                           ("curry"
                                                                                                                                                                                            ::
                                                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                                                           coe
                                                                                                                                                                             (case coe
                                                                                                                                                                                     v26 of
                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                                                                                  -> if coe
                                                                                                                                                                                          v27
                                                                                                                                                                                       then coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v28)
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 C_ahv'45'curry_1300)
                                                                                                                                                                                       else coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v28)
                                                                                                                                                                                              (let v29
                                                                                                                                                                                                     = coe
                                                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                         erased
                                                                                                                                                                                                         (\ v29 ->
                                                                                                                                                                                                            coe
                                                                                                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v1))
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               v1)
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               ("apply"
                                                                                                                                                                                                                ::
                                                                                                                                                                                                                Data.Text.Text))) in
                                                                                                                                                                                               coe
                                                                                                                                                                                                 (case coe
                                                                                                                                                                                                         v29 of
                                                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                                                                                                                      -> if coe
                                                                                                                                                                                                              v30
                                                                                                                                                                                                           then coe
                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v31)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     C_ahv'45'apply_1302)
                                                                                                                                                                                                           else coe
                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v31)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     C_ahv'45'other_1314)
                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v1 v2
        -> let v3 = coe C_ahv'45'other_1314 in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
                  -> let v5
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v5 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe ("pair" :: Data.Text.Text))) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                            -> if coe v6
                                 then coe seq (coe v7) (coe C_ahv'45'pair'45'applied_1306)
                                 else coe
                                        seq (coe v7)
                                        (let v8
                                               = coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                   erased
                                                   (\ v8 ->
                                                      coe
                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                        (coe v4))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                      (coe v4)
                                                      (coe ("compose" :: Data.Text.Text))) in
                                         coe
                                           (case coe v8 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                -> if coe v9
                                                     then coe
                                                            seq (coe v10)
                                                            (coe C_ahv'45'compose'45'applied_1310)
                                                     else coe
                                                            seq (coe v10) (coe C_ahv'45'other_1314)
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v1 v2
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v1 v2 v3
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v1 v2
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v1
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v1
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v1 v2
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v1 v2 v3
        -> coe C_ahv'45'other_1314
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v2
        -> coe C_ahv'45'other_1314
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.classifyAppHead-nothing⇒view-other
d_classifyAppHead'45'nothing'8658'view'45'other_1422 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHead'45'nothing'8658'view'45'other_1422 = erased
-- Once.TypeCheck.Elaborate.composeArgB
d_composeArgB_1668 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_38
d_composeArgB_1668 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> let v5
                    = let v5 = d_lookupPoly_428 (coe d_polys_524 (coe v0)) (coe v4) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                    -> coe
                                         MAlonzo.Code.Once.Type.d_schemaArrowCodomain_1222 (coe v7)
                                         (coe v2)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                           _ -> MAlonzo.RTE.mazUnreachableError) in
              coe
                (case coe v4 of
                   l | (==) l ("fst" :: Data.Text.Text) ->
                       case coe v2 of
                         MAlonzo.Code.Once.Type.C__'42'__52 v6 v7
                           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v6)
                         _ -> coe v5
                   l | (==) l ("id" :: Data.Text.Text) ->
                       coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                   l | (==) l ("snd" :: Data.Text.Text) ->
                       case coe v2 of
                         MAlonzo.Code.Once.Type.C__'42'__52 v6 v7
                           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
                         _ -> coe v5
                   l | (==) l ("terminal" :: Data.Text.Text) ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                         (coe MAlonzo.Code.Once.Type.C_Unit_48)
                   _ -> coe v5)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.BareBuiltinClass
d_BareBuiltinClass_1708 a0 = ()
data T_BareBuiltinClass_1708
  = C_bbc'45'id_1710 | C_bbc'45'fst_1712 | C_bbc'45'snd_1714 |
    C_bbc'45'terminal_1716 | C_bbc'45'initial_1718 |
    C_bbc'45'inl_1720 | C_bbc'45'inr_1722 | C_bbc'45'arr_1724 |
    C_bbc'45'other_1728
-- Once.TypeCheck.Elaborate.classifyBareBuiltin
d_classifyBareBuiltin_1732 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_BareBuiltinClass_1708
d_classifyBareBuiltin_1732 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v1 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe ("id" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then coe seq (coe v3) (coe C_bbc'45'id_1710)
                else coe
                       seq (coe v3)
                       (let v4
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v4 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v0))
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                                     (coe ("fst" :: Data.Text.Text))) in
                        coe
                          (case coe v4 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                               -> if coe v5
                                    then coe seq (coe v6) (coe C_bbc'45'fst_1712)
                                    else coe
                                           seq (coe v6)
                                           (let v7
                                                  = coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                      erased
                                                      (\ v7 ->
                                                         coe
                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                           (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                         (coe v0)
                                                         (coe ("snd" :: Data.Text.Text))) in
                                            coe
                                              (case coe v7 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                                   -> if coe v8
                                                        then coe
                                                               seq (coe v9) (coe C_bbc'45'snd_1714)
                                                        else coe
                                                               seq (coe v9)
                                                               (let v10
                                                                      = coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                          erased
                                                                          (\ v10 ->
                                                                             coe
                                                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                               (coe v0))
                                                                          (coe
                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                             (coe v0)
                                                                             (coe
                                                                                ("terminal"
                                                                                 ::
                                                                                 Data.Text.Text))) in
                                                                coe
                                                                  (case coe v10 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                       -> if coe v11
                                                                            then coe
                                                                                   seq (coe v12)
                                                                                   (coe
                                                                                      C_bbc'45'terminal_1716)
                                                                            else coe
                                                                                   seq (coe v12)
                                                                                   (let v13
                                                                                          = coe
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                              erased
                                                                                              (\ v13 ->
                                                                                                 coe
                                                                                                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                   (coe
                                                                                                      v0))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                 (coe
                                                                                                    v0)
                                                                                                 (coe
                                                                                                    ("initial"
                                                                                                     ::
                                                                                                     Data.Text.Text))) in
                                                                                    coe
                                                                                      (case coe
                                                                                              v13 of
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                                           -> if coe
                                                                                                   v14
                                                                                                then coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v15)
                                                                                                       (coe
                                                                                                          C_bbc'45'initial_1718)
                                                                                                else coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v15)
                                                                                                       (let v16
                                                                                                              = coe
                                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                  erased
                                                                                                                  (\ v16 ->
                                                                                                                     coe
                                                                                                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                       (coe
                                                                                                                          v0))
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                     (coe
                                                                                                                        v0)
                                                                                                                     (coe
                                                                                                                        ("inl"
                                                                                                                         ::
                                                                                                                         Data.Text.Text))) in
                                                                                                        coe
                                                                                                          (case coe
                                                                                                                  v16 of
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                                                               -> if coe
                                                                                                                       v17
                                                                                                                    then coe
                                                                                                                           seq
                                                                                                                           (coe
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              C_bbc'45'inl_1720)
                                                                                                                    else coe
                                                                                                                           seq
                                                                                                                           (coe
                                                                                                                              v18)
                                                                                                                           (let v19
                                                                                                                                  = coe
                                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                      erased
                                                                                                                                      (\ v19 ->
                                                                                                                                         coe
                                                                                                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                           (coe
                                                                                                                                              v0))
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                         (coe
                                                                                                                                            v0)
                                                                                                                                         (coe
                                                                                                                                            ("inr"
                                                                                                                                             ::
                                                                                                                                             Data.Text.Text))) in
                                                                                                                            coe
                                                                                                                              (case coe
                                                                                                                                      v19 of
                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                                                   -> if coe
                                                                                                                                           v20
                                                                                                                                        then coe
                                                                                                                                               seq
                                                                                                                                               (coe
                                                                                                                                                  v21)
                                                                                                                                               (coe
                                                                                                                                                  C_bbc'45'inr_1722)
                                                                                                                                        else coe
                                                                                                                                               seq
                                                                                                                                               (coe
                                                                                                                                                  v21)
                                                                                                                                               (let v22
                                                                                                                                                      = coe
                                                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                          erased
                                                                                                                                                          (\ v22 ->
                                                                                                                                                             coe
                                                                                                                                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                               (coe
                                                                                                                                                                  v0))
                                                                                                                                                          (coe
                                                                                                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                             (coe
                                                                                                                                                                v0)
                                                                                                                                                             (coe
                                                                                                                                                                ("arr"
                                                                                                                                                                 ::
                                                                                                                                                                 Data.Text.Text))) in
                                                                                                                                                coe
                                                                                                                                                  (case coe
                                                                                                                                                          v22 of
                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                                                                                       -> if coe
                                                                                                                                                               v23
                                                                                                                                                            then coe
                                                                                                                                                                   seq
                                                                                                                                                                   (coe
                                                                                                                                                                      v24)
                                                                                                                                                                   (coe
                                                                                                                                                                      C_bbc'45'arr_1724)
                                                                                                                                                            else coe
                                                                                                                                                                   seq
                                                                                                                                                                   (coe
                                                                                                                                                                      v24)
                                                                                                                                                                   (coe
                                                                                                                                                                      C_bbc'45'other_1728)
                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_1802 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_378
d_inferElab_1802 v0 v1
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
                                    (coe d_size_514 (coe v0)))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
                                 (coe (0 :: Integer)) (coe d_freshCounter_520 (coe v0)))
                       else coe
                              seq (coe v5)
                              (let v6
                                     = coe
                                         du_go_808 (coe v2) (coe d_size_514 (coe v0))
                                         (coe d_named_516 (coe v0)) (coe d_debruijn_518 (coe v0)) in
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
                                                         (coe d_freshCounter_520 (coe v0))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> let v7
                                               = d_lookupImport_716
                                                   (coe d_imports_522 (coe v0)) (coe v2) in
                                         coe
                                           (case coe v7 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                -> coe
                                                     C_success_392 (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                        (coe d_size_514 (coe v0)))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                        v2)
                                                     (coe (0 :: Integer))
                                                     (coe d_freshCounter_520 (coe v0))
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
                 = d_lookupImport_716
                     (coe d_imports_522 (coe v0))
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
                          (coe d_size_514 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("." :: Data.Text.Text) v2)))
                       (coe (0 :: Integer)) (coe d_freshCounter_520 (coe v0))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_394
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_UnboundQualified_14 (coe v2)
                          (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v2 v3
        -> let v4 = d_classifyAppHeadView_1318 (coe v2) in
           coe
             (case coe v4 of
                C_ahv'45'id_1284
                  -> let v5 = d_inferElab_1802 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_392 v6 v7 v8 v9 v10
                            -> coe
                                 C_success_392 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_514 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                    (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_514 (coe v0)))
                                    v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                       (coe d_debruijn_518 (coe v0))
                                       (coe
                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v6)
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6))
                                       (coe du_specId_596))
                                    v8)
                                 (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'fst_1286
                  -> let v5 = d_inferElab_1802 (coe v0) (coe v3) in
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
                                                 (coe d_size_514 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_514 (coe v0)))
                                              v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                 (coe d_debruijn_518 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                    (coe v6) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v12))
                                                 (coe du_specFst_604 (coe v13)))
                                              v8)
                                           (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                                    _ -> coe v11)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'snd_1288
                  -> let v5 = d_inferElab_1802 (coe v0) (coe v3) in
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
                                                 (coe d_size_514 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_514 (coe v0)))
                                              v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                 (coe d_debruijn_518 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                    (coe v6) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v13))
                                                 (coe du_specSnd_614 (coe v12)))
                                              v8)
                                           (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                                    _ -> coe v11)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'terminal_1290
                  -> let v5 = d_inferElab_1802 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_392 v6 v7 v8 v9 v10
                            -> coe
                                 C_success_392 (coe MAlonzo.Code.Once.Type.C_Unit_48)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_514 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                    (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_514 (coe v0)))
                                    v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                       (coe d_debruijn_518 (coe v0))
                                       (coe
                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v6)
                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                          (coe MAlonzo.Code.Once.Type.C_Unit_48))
                                       (coe du_specTerminal_658))
                                    v8)
                                 (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'inl_1292
                  -> coe
                       C_failure_394
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_20)
                C_ahv'45'inr_1294
                  -> coe
                       C_failure_394
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_22)
                C_ahv'45'initial_1296
                  -> coe
                       C_failure_394
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_24)
                C_ahv'45'arr_1298
                  -> let v5 = d_inferElab_1802 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_392 v6 v7 v8 v9 v10
                            -> let v11
                                     = coe
                                         C_failure_394
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_ArrNeedsFunction_34) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.Type.C_Many_10
                                             -> coe
                                                  C_success_392
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_Eff_58 (coe v12)
                                                     (coe v14))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                        (coe d_size_514 (coe v0)))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                        (coe v13) (coe v7)))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                     (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                        (coe d_size_514 (coe v0)))
                                                     v7
                                                     (MAlonzo.Code.Once.Type.d__'8658'__78
                                                        (coe v12) (coe v14))
                                                     v13
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                        (coe d_debruijn_518 (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                           (coe
                                                              MAlonzo.Code.Once.Type.d__'8658'__78
                                                              (coe v12) (coe v14))
                                                           (coe v13)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C_Eff_58
                                                              (coe v12) (coe v14)))
                                                        (coe du_specArr_710))
                                                     v8)
                                                  (coe addInt (coe (1 :: Integer)) (coe v9))
                                                  (coe v10)
                                           _ -> coe v11
                                    _ -> coe v11)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'curry_1300
                  -> coe
                       C_failure_394
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                          (coe ("curry" :: Data.Text.Text)))
                C_ahv'45'apply_1302
                  -> let v5 = d_inferElab_1802 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_392 v6 v7 v8 v9 v10
                            -> let v11
                                     = coe
                                         C_failure_394
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                            (coe ("apply" :: Data.Text.Text))) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Once.Type.C__'42'__52 v12 v13
                                      -> case coe v12 of
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v14 v15 v16
                                             -> case coe v15 of
                                                  MAlonzo.Code.Once.Type.C_Many_10
                                                    -> let v17
                                                             = d__'8799'T__16 (coe v14) (coe v13) in
                                                       coe
                                                         (case coe v17 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                              -> if coe v18
                                                                   then coe
                                                                          seq (coe v19)
                                                                          (coe
                                                                             C_success_392 (coe v16)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                   (coe
                                                                                      d_size_514
                                                                                      (coe v0)))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                   (coe v15)
                                                                                   (coe v7)))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                   (coe
                                                                                      d_size_514
                                                                                      (coe v0)))
                                                                                v7
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Type.C__'42'__52
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                      (coe v14)
                                                                                      (coe v16))
                                                                                   (coe v14))
                                                                                v15
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                   (coe
                                                                                      d_debruijn_518
                                                                                      (coe v0))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Type.C__'42'__52
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                            (coe
                                                                                               v14)
                                                                                            (coe
                                                                                               v16))
                                                                                         (coe v14))
                                                                                      (coe v15)
                                                                                      (coe v16))
                                                                                   (coe
                                                                                      d_specApply_686
                                                                                      (coe v14)
                                                                                      (coe v16)))
                                                                                v8)
                                                                             (coe
                                                                                addInt
                                                                                (coe (1 :: Integer))
                                                                                (coe v9))
                                                                             (coe v10))
                                                                   else coe
                                                                          seq (coe v19)
                                                                          (coe
                                                                             C_failure_394
                                                                             (coe
                                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                (coe
                                                                                   ("apply"
                                                                                    ::
                                                                                    Data.Text.Text))))
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> coe v11
                                           _ -> coe v11
                                    _ -> coe v11)
                          C_failure_394 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'pair'45'applied_1306
                  -> coe
                       C_failure_394
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                          (coe ("pair" :: Data.Text.Text)))
                C_ahv'45'compose'45'applied_1310
                  -> coe
                       C_failure_394
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                          (coe ("compose" :: Data.Text.Text)))
                C_ahv'45'other_1314
                  -> let v6
                           = coe du_asFun_1040 (coe d_inferElab_1802 (coe v0) (coe v2)) in
                     coe
                       (case coe v6 of
                          C_isFun_1024 v7 v8 v9 v10 v11 v12 v13
                            -> let v14 = d_inferElab_1802 (coe v0) (coe v3) in
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
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_ApplicationTypeMismatch_46
                                                                  (coe v7) (coe v15)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v15 -> coe v14
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_isEff_1032 v7 v8 v9 v10 v11 v12
                            -> let v13 = d_inferElab_1802 (coe v0) (coe v3) in
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
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_ApplicationTypeMismatch_46
                                                                  (coe v7) (coe v14)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v14 -> coe v13
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_notFun_1034 v7 -> coe C_failure_394 (coe v7)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v2 v3
        -> coe
             C_failure_394
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_16)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v2 v3 v4
        -> let v5 = d_inferElab_1802 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_392 v6 v7 v8 v9 v10
                  -> let v11
                           = d_inferElab_1802
                               (coe d_extendNamedCtx_558 (coe v0) (coe v2) (coe v6)) (coe v4) in
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
        -> let v4 = d_inferElab_1802 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_392 v5 v6 v7 v8 v9
                  -> let v10 = d_inferElab_1802 (coe v0) (coe v3) in
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
        -> let v7 = d_inferElab_1802 (coe v0) (coe v2) in
           coe
             (case coe v7 of
                C_success_392 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               C_failure_394
                               (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_38) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Once.Type.C__'43'__54 v14 v15
                            -> let v16
                                     = d_inferElab_1802
                                         (coe d_extendNamedCtx_558 (coe v0) (coe v3) (coe v14))
                                         (coe v4) in
                               coe
                                 (case coe v16 of
                                    C_success_392 v17 v18 v19 v20 v21
                                      -> case coe v18 of
                                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v23 v24
                                             -> let v25
                                                      = d_inferElab_1802
                                                          (coe
                                                             d_extendNamedCtx_558 (coe v0) (coe v5)
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
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_40))
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
                (coe d_size_514 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
             (coe (0 :: Integer)) (coe d_freshCounter_520 (coe v0))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v2
        -> coe
             C_success_392 (coe MAlonzo.Code.Once.Type.C_Int_64)
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_514 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_int_350 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_520 (coe v0))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v2
        -> coe
             C_success_392 (coe MAlonzo.Code.Once.Type.C_Str_68)
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_514 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_str_356 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_520 (coe v0))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v2 v3
        -> let v4 = d_checkElab_1808 (coe v0) (coe v2) (coe v3) in
           coe
             (case coe v4 of
                C_success_416 v5 v6 v7 v8
                  -> coe C_success_392 (coe v3) (coe v5) (coe v6) (coe v7) (coe v8)
                C_failure_418 v5 -> coe C_failure_394 (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v2 v3 v4
        -> let v5
                 = coe du_asInt_1114 (coe d_inferElab_1802 (coe v0) (coe v3)) in
           coe
             (case coe v5 of
                C_isInt_1106 v6 v7 v8 v9
                  -> let v10
                           = coe du_asInt_1114 (coe d_inferElab_1802 (coe v0) (coe v4)) in
                     coe
                       (case coe v10 of
                          C_isInt_1106 v11 v12 v13 v14
                            -> coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe MAlonzo.Code.Once.TypeCheck.Raw.d_isArithmeticOp_90 (coe v2))
                                 (coe
                                    C_success_392 (coe MAlonzo.Code.Once.Type.C_Int_64)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v6)
                                       (coe v11))
                                    (coe du_mkArith_3130 v6 v11 v2 v7 v12)
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
                                    (coe du_mkCmp_3138 v6 v11 v2 v7 v12)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v13))
                                    (coe v14))
                          C_notInt_1108 v11
                            -> coe
                                 C_failure_394
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_72
                                    (coe v11))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_notInt_1108 v6
                  -> coe
                       C_failure_394
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_70 (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v3
        -> let v4 = d_inferElab_1802 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                C_success_392 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               C_failure_394
                               (coe MAlonzo.Code.Once.TypeCheck.Error.C_NegationNotInt_36) in
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
d_checkElab_1808 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
d_checkElab_1808 v0 v1 v2
  = let v3
          = let v3 = d_inferElab_1802 (coe v0) (coe v1) in
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
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                               (coe v2) (coe v4)))
                           _ -> MAlonzo.RTE.mazUnreachableError)
                 C_failure_394 v4 -> coe C_failure_418 (coe v4)
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> coe d_checkElab'45'RVar_1816 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v4 v5
           -> let v6 = d_classifyAppHeadView_1318 (coe v4) in
              coe
                (case coe v6 of
                   C_ahv'45'id_1284
                     -> let v7 = d_inferElab_1802 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             C_success_392 v8 v9 v10 v11 v12
                               -> let v13
                                        = coe
                                            MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                            (coe
                                               MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                               (coe d_size_514 (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)) in
                                  coe
                                    (let v14
                                           = coe
                                               MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                               (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                  (coe d_size_514 (coe v0)))
                                               v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                  (coe d_debruijn_518 (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                     (coe v8) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v8))
                                                  (coe du_specId_596))
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
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
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
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v9 -> coe C_failure_418 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'fst_1286
                     -> let v7 = d_inferElab_1802 (coe v0) (coe v5) in
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
                                                      (coe d_size_514 (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)) in
                                         coe
                                           (let v16
                                                  = coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                      (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                         (coe d_size_514 (coe v0)))
                                                      v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                         (coe d_debruijn_518 (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                            (coe v8)
                                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                            (coe v13))
                                                         (coe du_specFst_604 (coe v14)))
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
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
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
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v9 -> coe C_failure_418 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'snd_1288
                     -> let v7 = d_inferElab_1802 (coe v0) (coe v5) in
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
                                                      (coe d_size_514 (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)) in
                                         coe
                                           (let v16
                                                  = coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                      (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                         (coe d_size_514 (coe v0)))
                                                      v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                         (coe d_debruijn_518 (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                            (coe v8)
                                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                            (coe v14))
                                                         (coe du_specSnd_614 (coe v13)))
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
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
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
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v9 -> coe C_failure_418 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'terminal_1290
                     -> let v7 = d_inferElab_1802 (coe v0) (coe v5) in
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
                                                  (coe d_size_514 (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe v9)) in
                                     coe
                                       (let v15
                                              = coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                  (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                     (coe d_size_514 (coe v0)))
                                                  v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                     (coe d_debruijn_518 (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                        (coe v8)
                                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                        (coe MAlonzo.Code.Once.Type.C_Unit_48))
                                                     (coe du_specTerminal_658))
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
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
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
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_394 v9 -> coe C_failure_418 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'inl_1292
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
                            -> let v9 = d_checkElab_1808 (coe v0) (coe v5) (coe v7) in
                               coe
                                 (case coe v9 of
                                    C_success_416 v10 v11 v12 v13
                                      -> coe
                                           C_success_416
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_514 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_514 (coe v0)))
                                              v10 v7 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                 (coe d_debruijn_518 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                    (coe v7) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v2))
                                                 (coe du_specInl_624))
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
                   C_ahv'45'inr_1294
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
                            -> let v9 = d_checkElab_1808 (coe v0) (coe v5) (coe v8) in
                               coe
                                 (case coe v9 of
                                    C_success_416 v10 v11 v12 v13
                                      -> coe
                                           C_success_416
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_514 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_514 (coe v0)))
                                              v10 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                 (coe d_debruijn_518 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                    (coe v8) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v2))
                                                 (coe du_specInr_634))
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
                   C_ahv'45'initial_1296
                     -> let v7
                              = d_checkElab_1808
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
                                          (coe d_size_514 (coe v0)))
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                       (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                          (coe d_size_514 (coe v0)))
                                       v8 (coe MAlonzo.Code.Once.Type.C_Void_50)
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                          (coe d_debruijn_518 (coe v0))
                                          (coe
                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                             (coe MAlonzo.Code.Once.Type.C_Void_50)
                                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                                          (coe du_specInitial_664))
                                       v9)
                                    (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11)
                             C_failure_418 v8 -> coe v7
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'arr_1298
                     -> case coe v2 of
                          MAlonzo.Code.Once.Type.C_Unit_48
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Void_50
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C__'42'__52 v7 v8
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C__'43'__54 v7 v8
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v7 v8 v9
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Eff_58 v7 v8
                            -> let v9
                                     = d_checkElab_1808
                                         (coe v0) (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v7)
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)) in
                               coe
                                 (case coe v9 of
                                    C_success_416 v10 v11 v12 v13
                                      -> coe
                                           C_success_416
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_514 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_514 (coe v0)))
                                              v10
                                              (MAlonzo.Code.Once.Type.d__'8658'__78
                                                 (coe v7) (coe v8))
                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                 (coe d_debruijn_518 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                    (coe
                                                       MAlonzo.Code.Once.Type.d__'8658'__78 (coe v7)
                                                       (coe v8))
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                                                 (coe du_specArr_710))
                                              v11)
                                           (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                                    C_failure_418 v10 -> coe v9
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.Type.C_μ'45'type_60 v7
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_ν'45'type_62 v7
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Int_64
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Float_66
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Str_68
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Buffer_70
                            -> coe
                                 C_failure_418
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'curry_1300
                     -> coe d_checkCurry_1844 (coe v0) (coe v5) (coe v2)
                   C_ahv'45'apply_1302
                     -> coe d_checkApply_1852 (coe v0) (coe v5) (coe v2)
                   C_ahv'45'pair'45'applied_1306
                     -> case coe v4 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v8 v9
                            -> coe
                                 d_checkPair_1826 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                       (coe ("pair" :: Data.Text.Text)))
                                    (coe v9))
                                 (coe v5) (coe v2)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'compose'45'applied_1310
                     -> case coe v4 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v8 v9
                            -> coe
                                 d_checkCompose_1836 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                       (coe ("compose" :: Data.Text.Text)))
                                    (coe v9))
                                 (coe v5) (coe v2)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'other_1314
                     -> let v8
                              = coe du_asFun_1040 (coe d_inferElab_1802 (coe v0) (coe v4)) in
                        coe
                          (case coe v8 of
                             C_isFun_1024 v9 v10 v11 v12 v13 v14 v15
                               -> let v16 = d_inferElab_1802 (coe v0) (coe v5) in
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
                                                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
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
                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_ApplicationTypeMismatch_46
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
                                                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
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
                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                            (coe v2) (coe v18)))
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              C_failure_394 v18 -> coe C_failure_418 (coe v18)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             C_isEff_1032 v9 v10 v11 v12 v13 v14
                               -> let v15 = d_inferElab_1802 (coe v0) (coe v5) in
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
                                                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
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
                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_ApplicationTypeMismatch_46
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
                                                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
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
                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                            (coe v2) (coe v17)))
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              C_failure_394 v17 -> coe C_failure_418 (coe v17)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             C_notFun_1034 v9 -> coe C_failure_418 (coe v9)
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
                              = d_checkElab_1808
                                  (coe d_extendNamedCtx_558 (coe v0) (coe v4) (coe v7)) (coe v5)
                                  (coe v9) in
                        coe
                          (case coe v10 of
                             C_success_416 v11 v12 v13 v14
                               -> case coe v11 of
                                    MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v16 v17
                                      -> let v18 = d_decideLeq_1152 (coe v16) (coe v8) in
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
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_64
                                                        (coe v4) (coe v8) (coe v16))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             C_failure_418 v11 -> coe v10
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v6)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkElab-RVar
d_checkElab'45'RVar_1816 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
d_checkElab'45'RVar_1816 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v3 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                 (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
                 (coe
                    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                    ("id" :: Data.Text.Text))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then let v6 = seq (coe v5) (coe C_bbc'45'id_1710) in
                     coe
                       (case coe v6 of
                          C_bbc'45'id_1710
                            -> let v7 = "id" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_808 (coe ("id" :: Data.Text.Text))
                                            (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                            (coe d_debruijn_518 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_520 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__16
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_416
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_418
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_716
                                                      (coe d_imports_522 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_514 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_520
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__16
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_416
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_418
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_418 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                -> case coe v13 of
                                                                     MAlonzo.Code.Once.Type.C_Many_10
                                                                       -> let v15
                                                                                = d__'8799'T__16
                                                                                    (coe v12)
                                                                                    (coe v14) in
                                                                          coe
                                                                            (case coe v15 of
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                 -> if coe v16
                                                                                      then coe
                                                                                             seq
                                                                                             (coe
                                                                                                v17)
                                                                                             (coe
                                                                                                C_success_416
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                   (coe
                                                                                                      d_size_514
                                                                                                      (coe
                                                                                                         v0)))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                   (coe
                                                                                                      d_debruijn_518
                                                                                                      (coe
                                                                                                         v0))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                      (coe
                                                                                                         v12)
                                                                                                      (coe
                                                                                                         v13)
                                                                                                      (coe
                                                                                                         v12))
                                                                                                   (coe
                                                                                                      du_specId_596))
                                                                                                (coe
                                                                                                   (0 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   d_freshCounter_520
                                                                                                   (coe
                                                                                                      v0)))
                                                                                      else coe
                                                                                             seq
                                                                                             (coe
                                                                                                v17)
                                                                                             (coe
                                                                                                C_failure_418
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                   (coe
                                                                                                      ("id"
                                                                                                       ::
                                                                                                       Data.Text.Text))))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'fst_1712
                            -> let v7 = "fst" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_808 (coe ("fst" :: Data.Text.Text))
                                            (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                            (coe d_debruijn_518 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_520 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__16
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_416
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_418
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_716
                                                      (coe d_imports_522 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_514 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_520
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__16
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_416
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_418
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_418 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                -> case coe v12 of
                                                                     MAlonzo.Code.Once.Type.C__'42'__52 v15 v16
                                                                       -> case coe v13 of
                                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                                              -> let v17
                                                                                       = d__'8799'T__16
                                                                                           (coe v15)
                                                                                           (coe
                                                                                              v14) in
                                                                                 coe
                                                                                   (case coe v17 of
                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                        -> if coe
                                                                                                v18
                                                                                             then coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v19)
                                                                                                    (coe
                                                                                                       C_success_416
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_514
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                          (coe
                                                                                                             d_debruijn_518
                                                                                                             (coe
                                                                                                                v0))
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                             (coe
                                                                                                                v12)
                                                                                                             (coe
                                                                                                                v13)
                                                                                                             (coe
                                                                                                                v15))
                                                                                                          (coe
                                                                                                             du_specFst_604
                                                                                                             (coe
                                                                                                                v16)))
                                                                                                       (coe
                                                                                                          (0 ::
                                                                                                             Integer))
                                                                                                       (coe
                                                                                                          d_freshCounter_520
                                                                                                          (coe
                                                                                                             v0)))
                                                                                             else coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v19)
                                                                                                    (coe
                                                                                                       C_failure_418
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                          (coe
                                                                                                             ("fst"
                                                                                                              ::
                                                                                                              Data.Text.Text))))
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                            _ -> coe v11
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'snd_1714
                            -> let v7 = "snd" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_808 (coe ("snd" :: Data.Text.Text))
                                            (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                            (coe d_debruijn_518 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_520 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__16
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_416
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_418
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_716
                                                      (coe d_imports_522 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_514 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_520
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__16
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_416
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_418
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_418 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                -> case coe v12 of
                                                                     MAlonzo.Code.Once.Type.C__'42'__52 v15 v16
                                                                       -> case coe v13 of
                                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                                              -> let v17
                                                                                       = d__'8799'T__16
                                                                                           (coe v16)
                                                                                           (coe
                                                                                              v14) in
                                                                                 coe
                                                                                   (case coe v17 of
                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                        -> if coe
                                                                                                v18
                                                                                             then coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v19)
                                                                                                    (coe
                                                                                                       C_success_416
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_514
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                          (coe
                                                                                                             d_debruijn_518
                                                                                                             (coe
                                                                                                                v0))
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                             (coe
                                                                                                                v12)
                                                                                                             (coe
                                                                                                                v13)
                                                                                                             (coe
                                                                                                                v16))
                                                                                                          (coe
                                                                                                             du_specSnd_614
                                                                                                             (coe
                                                                                                                v15)))
                                                                                                       (coe
                                                                                                          (0 ::
                                                                                                             Integer))
                                                                                                       (coe
                                                                                                          d_freshCounter_520
                                                                                                          (coe
                                                                                                             v0)))
                                                                                             else coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v19)
                                                                                                    (coe
                                                                                                       C_failure_418
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                          (coe
                                                                                                             ("snd"
                                                                                                              ::
                                                                                                              Data.Text.Text))))
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                            _ -> coe v11
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'terminal_1716
                            -> let v7 = "terminal" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_808 (coe ("terminal" :: Data.Text.Text))
                                            (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                            (coe d_debruijn_518 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_520 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__16
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_416
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_418
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_716
                                                      (coe d_imports_522 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_514 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_520
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__16
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_416
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_418
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_418 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                -> case coe v13 of
                                                                     MAlonzo.Code.Once.Type.C_Many_10
                                                                       -> case coe v14 of
                                                                            MAlonzo.Code.Once.Type.C_Unit_48
                                                                              -> coe
                                                                                   C_success_416
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                      (coe
                                                                                         d_size_514
                                                                                         (coe v0)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                      (coe
                                                                                         d_debruijn_518
                                                                                         (coe v0))
                                                                                      (coe v2)
                                                                                      (coe
                                                                                         du_specTerminal_658))
                                                                                   (coe
                                                                                      (0 ::
                                                                                         Integer))
                                                                                   (coe
                                                                                      d_freshCounter_520
                                                                                      (coe v0))
                                                                            _ -> coe v11
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'initial_1718
                            -> let v7 = "initial" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_808 (coe ("initial" :: Data.Text.Text))
                                            (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                            (coe d_debruijn_518 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_520 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__16
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_416
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_418
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_716
                                                      (coe d_imports_522 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_514 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_520
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__16
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_416
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_418
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_418 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                -> case coe v12 of
                                                                     MAlonzo.Code.Once.Type.C_Void_50
                                                                       -> case coe v13 of
                                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                                              -> coe
                                                                                   C_success_416
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                      (coe
                                                                                         d_size_514
                                                                                         (coe v0)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                      (coe
                                                                                         d_debruijn_518
                                                                                         (coe v0))
                                                                                      (coe v2)
                                                                                      (coe
                                                                                         du_specInitial_664))
                                                                                   (coe
                                                                                      (0 ::
                                                                                         Integer))
                                                                                   (coe
                                                                                      d_freshCounter_520
                                                                                      (coe v0))
                                                                            _ -> coe v11
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'inl_1720
                            -> let v7 = "inl" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_808 (coe ("inl" :: Data.Text.Text))
                                            (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                            (coe d_debruijn_518 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_520 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__16
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_416
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_418
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_716
                                                      (coe d_imports_522 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_514 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_520
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__16
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_416
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_418
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_418 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                -> case coe v13 of
                                                                     MAlonzo.Code.Once.Type.C_Many_10
                                                                       -> case coe v14 of
                                                                            MAlonzo.Code.Once.Type.C__'43'__54 v15 v16
                                                                              -> let v17
                                                                                       = d__'8799'T__16
                                                                                           (coe v12)
                                                                                           (coe
                                                                                              v15) in
                                                                                 coe
                                                                                   (case coe v17 of
                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                        -> if coe
                                                                                                v18
                                                                                             then coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v19)
                                                                                                    (coe
                                                                                                       C_success_416
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_514
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                          (coe
                                                                                                             d_debruijn_518
                                                                                                             (coe
                                                                                                                v0))
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                             (coe
                                                                                                                v12)
                                                                                                             (coe
                                                                                                                v13)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Type.C__'43'__54
                                                                                                                (coe
                                                                                                                   v12)
                                                                                                                (coe
                                                                                                                   v16)))
                                                                                                          (coe
                                                                                                             du_specInl_624))
                                                                                                       (coe
                                                                                                          (0 ::
                                                                                                             Integer))
                                                                                                       (coe
                                                                                                          d_freshCounter_520
                                                                                                          (coe
                                                                                                             v0)))
                                                                                             else coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v19)
                                                                                                    (coe
                                                                                                       C_failure_418
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                          (coe
                                                                                                             ("inl"
                                                                                                              ::
                                                                                                              Data.Text.Text))))
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                            _ -> coe v11
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'inr_1722
                            -> let v7 = "inr" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_808 (coe ("inr" :: Data.Text.Text))
                                            (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                            (coe d_debruijn_518 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_520 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__16
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_416
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_418
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_716
                                                      (coe d_imports_522 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_514 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_520
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__16
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_416
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_418
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_418 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                -> case coe v13 of
                                                                     MAlonzo.Code.Once.Type.C_Many_10
                                                                       -> case coe v14 of
                                                                            MAlonzo.Code.Once.Type.C__'43'__54 v15 v16
                                                                              -> let v17
                                                                                       = d__'8799'T__16
                                                                                           (coe v12)
                                                                                           (coe
                                                                                              v16) in
                                                                                 coe
                                                                                   (case coe v17 of
                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                        -> if coe
                                                                                                v18
                                                                                             then coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v19)
                                                                                                    (coe
                                                                                                       C_success_416
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_514
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                          (coe
                                                                                                             d_debruijn_518
                                                                                                             (coe
                                                                                                                v0))
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                             (coe
                                                                                                                v12)
                                                                                                             (coe
                                                                                                                v13)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Type.C__'43'__54
                                                                                                                (coe
                                                                                                                   v15)
                                                                                                                (coe
                                                                                                                   v12)))
                                                                                                          (coe
                                                                                                             du_specInr_634))
                                                                                                       (coe
                                                                                                          (0 ::
                                                                                                             Integer))
                                                                                                       (coe
                                                                                                          d_freshCounter_520
                                                                                                          (coe
                                                                                                             v0)))
                                                                                             else coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v19)
                                                                                                    (coe
                                                                                                       C_failure_418
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                          (coe
                                                                                                             ("inr"
                                                                                                              ::
                                                                                                              Data.Text.Text))))
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                            _ -> coe v11
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'arr_1724
                            -> let v7 = "arr" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_808 (coe ("arr" :: Data.Text.Text))
                                            (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                            (coe d_debruijn_518 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_520 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__16
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_416
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_418
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_716
                                                      (coe d_imports_522 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_514 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_520
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__16
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_416
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_418
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_418 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                -> case coe v12 of
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v15 v16 v17
                                                                       -> case coe v16 of
                                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                                              -> case coe v13 of
                                                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                                                     -> case coe
                                                                                               v14 of
                                                                                          MAlonzo.Code.Once.Type.C_Eff_58 v18 v19
                                                                                            -> let v20
                                                                                                     = d__'8799'T__16
                                                                                                         (coe
                                                                                                            v15)
                                                                                                         (coe
                                                                                                            v18) in
                                                                                               coe
                                                                                                 (let v21
                                                                                                        = d__'8799'T__16
                                                                                                            (coe
                                                                                                               v17)
                                                                                                            (coe
                                                                                                               v19) in
                                                                                                  coe
                                                                                                    (case coe
                                                                                                            v20 of
                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                         -> let v24
                                                                                                                  = coe
                                                                                                                      C_failure_418
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                         (coe
                                                                                                                            ("arr"
                                                                                                                             ::
                                                                                                                             Data.Text.Text))) in
                                                                                                            coe
                                                                                                              (case coe
                                                                                                                      v22 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                   -> case coe
                                                                                                                             v23 of
                                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                                                                          -> case coe
                                                                                                                                    v21 of
                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                                                 -> case coe
                                                                                                                                           v26 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                                        -> case coe
                                                                                                                                                  v27 of
                                                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v28
                                                                                                                                               -> coe
                                                                                                                                                    C_success_416
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                                                       (coe
                                                                                                                                                          d_size_514
                                                                                                                                                          (coe
                                                                                                                                                             v0)))
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                                                                       (coe
                                                                                                                                                          d_debruijn_518
                                                                                                                                                          (coe
                                                                                                                                                             v0))
                                                                                                                                                       (coe
                                                                                                                                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                                                                          (coe
                                                                                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                                                                             (coe
                                                                                                                                                                v15)
                                                                                                                                                             (coe
                                                                                                                                                                v13)
                                                                                                                                                             (coe
                                                                                                                                                                v17))
                                                                                                                                                          (coe
                                                                                                                                                             v13)
                                                                                                                                                          (coe
                                                                                                                                                             MAlonzo.Code.Once.Type.C_Eff_58
                                                                                                                                                             (coe
                                                                                                                                                                v15)
                                                                                                                                                             (coe
                                                                                                                                                                v17)))
                                                                                                                                                       (coe
                                                                                                                                                          du_specArr_710))
                                                                                                                                                    (coe
                                                                                                                                                       (0 ::
                                                                                                                                                          Integer))
                                                                                                                                                    (coe
                                                                                                                                                       d_freshCounter_520
                                                                                                                                                       (coe
                                                                                                                                                          v0))
                                                                                                                                             _ -> coe
                                                                                                                                                    v24
                                                                                                                                      _ -> coe
                                                                                                                                             v24
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> coe
                                                                                                                               v24
                                                                                                                 _ -> coe
                                                                                                                        v24)
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                          _ -> coe
                                                                                                 v11
                                                                                   _ -> coe v11
                                                                            _ -> coe v11
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'other_1728
                            -> let v8
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v8 ->
                                            coe
                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                              (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                            (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                               v1)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                               ("unit" :: Data.Text.Text))) in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                      -> if coe v9
                                           then let v11
                                                      = seq
                                                          (coe v10)
                                                          (coe
                                                             C_success_392
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_48)
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_514 (coe v0)))
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
                                                             (coe (0 :: Integer))
                                                             (coe d_freshCounter_520 (coe v0))) in
                                                coe
                                                  (case coe v11 of
                                                     C_success_392 v12 v13 v14 v15 v16
                                                       -> let v17
                                                                = d__'8799'T__16
                                                                    (coe v2) (coe v12) in
                                                          coe
                                                            (case coe v17 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                 -> if coe v18
                                                                      then coe
                                                                             seq (coe v19)
                                                                             (coe
                                                                                C_success_416
                                                                                (coe v13) (coe v14)
                                                                                (coe v15) (coe v16))
                                                                      else coe
                                                                             seq (coe v19)
                                                                             (coe
                                                                                C_failure_418
                                                                                (coe
                                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                   (coe v2)
                                                                                   (coe v12)))
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     C_failure_394 v12
                                                       -> let v13
                                                                = d_lookupPoly_428
                                                                    (coe d_polys_524 (coe v0))
                                                                    (coe v1) in
                                                          coe
                                                            (case coe v13 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                 -> case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                        -> let v17
                                                                                 = d_checkElab_1808
                                                                                     (coe
                                                                                        d_ctxWithImportsAndPolys_534
                                                                                        (coe
                                                                                           d_imports_522
                                                                                           (coe v0))
                                                                                        (coe
                                                                                           d_removePoly_464
                                                                                           (coe v1)
                                                                                           (coe
                                                                                              d_polys_524
                                                                                              (coe
                                                                                                 v0))))
                                                                                     (coe v16)
                                                                                     (coe v2) in
                                                                           coe
                                                                             (case coe v17 of
                                                                                C_success_416 v18 v19 v20 v21
                                                                                  -> coe
                                                                                       seq (coe v18)
                                                                                       (coe
                                                                                          C_success_416
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                             (coe
                                                                                                d_size_514
                                                                                                (coe
                                                                                                   v0)))
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                             (coe
                                                                                                d_debruijn_518
                                                                                                (coe
                                                                                                   v0))
                                                                                             (coe
                                                                                                v2)
                                                                                             (coe
                                                                                                v19))
                                                                                          (coe v20)
                                                                                          (coe v21))
                                                                                C_failure_418 v18
                                                                                  -> coe v17
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                 -> coe C_failure_418 (coe v12)
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           else (let v11
                                                       = seq
                                                           (coe v10)
                                                           (let v11
                                                                  = coe
                                                                      du_go_808 (coe v1)
                                                                      (coe d_size_514 (coe v0))
                                                                      (coe d_named_516 (coe v0))
                                                                      (coe
                                                                         d_debruijn_518 (coe v0)) in
                                                            coe
                                                              (case coe v11 of
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                          -> case coe v14 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                 -> coe
                                                                                      C_success_392
                                                                                      (coe v13)
                                                                                      (coe v15)
                                                                                      (coe v16)
                                                                                      (coe
                                                                                         (0 ::
                                                                                            Integer))
                                                                                      (coe
                                                                                         d_freshCounter_520
                                                                                         (coe v0))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                   -> let v12
                                                                            = d_lookupImport_716
                                                                                (coe
                                                                                   d_imports_522
                                                                                   (coe v0))
                                                                                (coe v1) in
                                                                      coe
                                                                        (case coe v12 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                             -> coe
                                                                                  C_success_392
                                                                                  (coe v13)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                     (coe
                                                                                        d_size_514
                                                                                        (coe v0)))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                                     v1)
                                                                                  (coe
                                                                                     (0 :: Integer))
                                                                                  (coe
                                                                                     d_freshCounter_520
                                                                                     (coe v0))
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> coe
                                                                                  C_failure_394
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                                     (coe v1))
                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                 coe
                                                   (case coe v11 of
                                                      C_success_392 v12 v13 v14 v15 v16
                                                        -> let v17
                                                                 = d__'8799'T__16
                                                                     (coe v2) (coe v12) in
                                                           coe
                                                             (case coe v17 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                  -> if coe v18
                                                                       then coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 C_success_416
                                                                                 (coe v13) (coe v14)
                                                                                 (coe v15)
                                                                                 (coe v16))
                                                                       else coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 C_failure_418
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                    (coe v2)
                                                                                    (coe v12)))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      C_failure_394 v12
                                                        -> let v13
                                                                 = d_lookupPoly_428
                                                                     (coe d_polys_524 (coe v0))
                                                                     (coe v1) in
                                                           coe
                                                             (case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                         -> let v17
                                                                                  = d_checkElab_1808
                                                                                      (coe
                                                                                         d_ctxWithImportsAndPolys_534
                                                                                         (coe
                                                                                            d_imports_522
                                                                                            (coe
                                                                                               v0))
                                                                                         (coe
                                                                                            d_removePoly_464
                                                                                            (coe v1)
                                                                                            (coe
                                                                                               d_polys_524
                                                                                               (coe
                                                                                                  v0))))
                                                                                      (coe v16)
                                                                                      (coe v2) in
                                                                            coe
                                                                              (case coe v17 of
                                                                                 C_success_416 v18 v19 v20 v21
                                                                                   -> coe
                                                                                        seq
                                                                                        (coe v18)
                                                                                        (coe
                                                                                           C_success_416
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                              (coe
                                                                                                 d_size_514
                                                                                                 (coe
                                                                                                    v0)))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                              (coe
                                                                                                 d_debruijn_518
                                                                                                 (coe
                                                                                                    v0))
                                                                                              (coe
                                                                                                 v2)
                                                                                              (coe
                                                                                                 v19))
                                                                                           (coe v20)
                                                                                           (coe
                                                                                              v21))
                                                                                 C_failure_418 v18
                                                                                   -> coe v17
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe C_failure_418 (coe v12)
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else (let v6
                            = seq
                                (coe v5)
                                (let v6
                                       = coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                           erased
                                           (\ v6 ->
                                              coe
                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                (coe v1))
                                           (coe
                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                              (coe v1) (coe ("fst" :: Data.Text.Text))) in
                                 coe
                                   (case coe v6 of
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                        -> if coe v7
                                             then coe seq (coe v8) (coe C_bbc'45'fst_1712)
                                             else coe
                                                    seq (coe v8)
                                                    (let v9
                                                           = coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                               erased
                                                               (\ v9 ->
                                                                  coe
                                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                    (coe v1))
                                                               (coe
                                                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                  (coe v1)
                                                                  (coe
                                                                     ("snd" :: Data.Text.Text))) in
                                                     coe
                                                       (case coe v9 of
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                            -> if coe v10
                                                                 then coe
                                                                        seq (coe v11)
                                                                        (coe C_bbc'45'snd_1714)
                                                                 else coe
                                                                        seq (coe v11)
                                                                        (let v12
                                                                               = coe
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                   erased
                                                                                   (\ v12 ->
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
                                                                           (case coe v12 of
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                                                -> if coe v13
                                                                                     then coe
                                                                                            seq
                                                                                            (coe
                                                                                               v14)
                                                                                            (coe
                                                                                               C_bbc'45'terminal_1716)
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
                                                                                                       v15 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                                    -> if coe
                                                                                                            v16
                                                                                                         then coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v17)
                                                                                                                (coe
                                                                                                                   C_bbc'45'initial_1718)
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
                                                                                                                           v18 of
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                                                        -> if coe
                                                                                                                                v19
                                                                                                                             then coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v20)
                                                                                                                                    (coe
                                                                                                                                       C_bbc'45'inl_1720)
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
                                                                                                                                               v21 of
                                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                                                            -> if coe
                                                                                                                                                    v22
                                                                                                                                                 then coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (coe
                                                                                                                                                           C_bbc'45'inr_1722)
                                                                                                                                                 else coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (let v24
                                                                                                                                                               = coe
                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                   erased
                                                                                                                                                                   (\ v24 ->
                                                                                                                                                                      coe
                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                        (coe
                                                                                                                                                                           v1))
                                                                                                                                                                   (coe
                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                      (coe
                                                                                                                                                                         v1)
                                                                                                                                                                      (coe
                                                                                                                                                                         ("arr"
                                                                                                                                                                          ::
                                                                                                                                                                          Data.Text.Text))) in
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
                                                                                                                                                                               C_bbc'45'arr_1724)
                                                                                                                                                                     else coe
                                                                                                                                                                            seq
                                                                                                                                                                            (coe
                                                                                                                                                                               v26)
                                                                                                                                                                            (coe
                                                                                                                                                                               C_bbc'45'other_1728)
                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                      _ -> MAlonzo.RTE.mazUnreachableError)) in
                      coe
                        (case coe v6 of
                           C_bbc'45'id_1710
                             -> let v7 = "id" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_808 (coe ("id" :: Data.Text.Text))
                                             (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                             (coe d_debruijn_518 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_520 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__16
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_416
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_418
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_716
                                                       (coe d_imports_522 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_514 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_520
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__16
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_416
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_418
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_418 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C_Many_10
                                                                        -> let v15
                                                                                 = d__'8799'T__16
                                                                                     (coe v12)
                                                                                     (coe v14) in
                                                                           coe
                                                                             (case coe v15 of
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                  -> if coe v16
                                                                                       then coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v17)
                                                                                              (coe
                                                                                                 C_success_416
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                    (coe
                                                                                                       d_size_514
                                                                                                       (coe
                                                                                                          v0)))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                    (coe
                                                                                                       d_debruijn_518
                                                                                                       (coe
                                                                                                          v0))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                       (coe
                                                                                                          v12)
                                                                                                       (coe
                                                                                                          v13)
                                                                                                       (coe
                                                                                                          v12))
                                                                                                    (coe
                                                                                                       du_specId_596))
                                                                                                 (coe
                                                                                                    (0 ::
                                                                                                       Integer))
                                                                                                 (coe
                                                                                                    d_freshCounter_520
                                                                                                    (coe
                                                                                                       v0)))
                                                                                       else coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v17)
                                                                                              (coe
                                                                                                 C_failure_418
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                    (coe
                                                                                                       ("id"
                                                                                                        ::
                                                                                                        Data.Text.Text))))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'fst_1712
                             -> let v7 = "fst" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_808 (coe ("fst" :: Data.Text.Text))
                                             (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                             (coe d_debruijn_518 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_520 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__16
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_416
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_418
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_716
                                                       (coe d_imports_522 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_514 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_520
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__16
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_416
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_418
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_418 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Once.Type.C__'42'__52 v15 v16
                                                                        -> case coe v13 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> let v17
                                                                                        = d__'8799'T__16
                                                                                            (coe
                                                                                               v15)
                                                                                            (coe
                                                                                               v14) in
                                                                                  coe
                                                                                    (case coe v17 of
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                         -> if coe
                                                                                                 v18
                                                                                              then coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (coe
                                                                                                        C_success_416
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                           (coe
                                                                                                              d_size_514
                                                                                                              (coe
                                                                                                                 v0)))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                           (coe
                                                                                                              d_debruijn_518
                                                                                                              (coe
                                                                                                                 v0))
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                              (coe
                                                                                                                 v12)
                                                                                                              (coe
                                                                                                                 v13)
                                                                                                              (coe
                                                                                                                 v15))
                                                                                                           (coe
                                                                                                              du_specFst_604
                                                                                                              (coe
                                                                                                                 v16)))
                                                                                                        (coe
                                                                                                           (0 ::
                                                                                                              Integer))
                                                                                                        (coe
                                                                                                           d_freshCounter_520
                                                                                                           (coe
                                                                                                              v0)))
                                                                                              else coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (coe
                                                                                                        C_failure_418
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                           (coe
                                                                                                              ("fst"
                                                                                                               ::
                                                                                                               Data.Text.Text))))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                             _ -> coe v11
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'snd_1714
                             -> let v7 = "snd" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_808 (coe ("snd" :: Data.Text.Text))
                                             (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                             (coe d_debruijn_518 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_520 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__16
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_416
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_418
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_716
                                                       (coe d_imports_522 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_514 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_520
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__16
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_416
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_418
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_418 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Once.Type.C__'42'__52 v15 v16
                                                                        -> case coe v13 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> let v17
                                                                                        = d__'8799'T__16
                                                                                            (coe
                                                                                               v16)
                                                                                            (coe
                                                                                               v14) in
                                                                                  coe
                                                                                    (case coe v17 of
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                         -> if coe
                                                                                                 v18
                                                                                              then coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (coe
                                                                                                        C_success_416
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                           (coe
                                                                                                              d_size_514
                                                                                                              (coe
                                                                                                                 v0)))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                           (coe
                                                                                                              d_debruijn_518
                                                                                                              (coe
                                                                                                                 v0))
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                              (coe
                                                                                                                 v12)
                                                                                                              (coe
                                                                                                                 v13)
                                                                                                              (coe
                                                                                                                 v16))
                                                                                                           (coe
                                                                                                              du_specSnd_614
                                                                                                              (coe
                                                                                                                 v15)))
                                                                                                        (coe
                                                                                                           (0 ::
                                                                                                              Integer))
                                                                                                        (coe
                                                                                                           d_freshCounter_520
                                                                                                           (coe
                                                                                                              v0)))
                                                                                              else coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (coe
                                                                                                        C_failure_418
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                           (coe
                                                                                                              ("snd"
                                                                                                               ::
                                                                                                               Data.Text.Text))))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                             _ -> coe v11
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'terminal_1716
                             -> let v7 = "terminal" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_808 (coe ("terminal" :: Data.Text.Text))
                                             (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                             (coe d_debruijn_518 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_520 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__16
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_416
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_418
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_716
                                                       (coe d_imports_522 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_514 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_520
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__16
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_416
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_418
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_418 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C_Many_10
                                                                        -> case coe v14 of
                                                                             MAlonzo.Code.Once.Type.C_Unit_48
                                                                               -> coe
                                                                                    C_success_416
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                       (coe
                                                                                          d_size_514
                                                                                          (coe v0)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                       (coe
                                                                                          d_debruijn_518
                                                                                          (coe v0))
                                                                                       (coe v2)
                                                                                       (coe
                                                                                          du_specTerminal_658))
                                                                                    (coe
                                                                                       (0 ::
                                                                                          Integer))
                                                                                    (coe
                                                                                       d_freshCounter_520
                                                                                       (coe v0))
                                                                             _ -> coe v11
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'initial_1718
                             -> let v7 = "initial" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_808 (coe ("initial" :: Data.Text.Text))
                                             (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                             (coe d_debruijn_518 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_520 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__16
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_416
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_418
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_716
                                                       (coe d_imports_522 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_514 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_520
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__16
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_416
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_418
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_418 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Once.Type.C_Void_50
                                                                        -> case coe v13 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> coe
                                                                                    C_success_416
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                       (coe
                                                                                          d_size_514
                                                                                          (coe v0)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                       (coe
                                                                                          d_debruijn_518
                                                                                          (coe v0))
                                                                                       (coe v2)
                                                                                       (coe
                                                                                          du_specInitial_664))
                                                                                    (coe
                                                                                       (0 ::
                                                                                          Integer))
                                                                                    (coe
                                                                                       d_freshCounter_520
                                                                                       (coe v0))
                                                                             _ -> coe v11
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'inl_1720
                             -> let v7 = "inl" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_808 (coe ("inl" :: Data.Text.Text))
                                             (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                             (coe d_debruijn_518 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_520 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__16
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_416
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_418
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_716
                                                       (coe d_imports_522 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_514 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_520
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__16
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_416
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_418
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_418 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C_Many_10
                                                                        -> case coe v14 of
                                                                             MAlonzo.Code.Once.Type.C__'43'__54 v15 v16
                                                                               -> let v17
                                                                                        = d__'8799'T__16
                                                                                            (coe
                                                                                               v12)
                                                                                            (coe
                                                                                               v15) in
                                                                                  coe
                                                                                    (case coe v17 of
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                         -> if coe
                                                                                                 v18
                                                                                              then coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (coe
                                                                                                        C_success_416
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                           (coe
                                                                                                              d_size_514
                                                                                                              (coe
                                                                                                                 v0)))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                           (coe
                                                                                                              d_debruijn_518
                                                                                                              (coe
                                                                                                                 v0))
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                              (coe
                                                                                                                 v12)
                                                                                                              (coe
                                                                                                                 v13)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.Type.C__'43'__54
                                                                                                                 (coe
                                                                                                                    v12)
                                                                                                                 (coe
                                                                                                                    v16)))
                                                                                                           (coe
                                                                                                              du_specInl_624))
                                                                                                        (coe
                                                                                                           (0 ::
                                                                                                              Integer))
                                                                                                        (coe
                                                                                                           d_freshCounter_520
                                                                                                           (coe
                                                                                                              v0)))
                                                                                              else coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (coe
                                                                                                        C_failure_418
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                           (coe
                                                                                                              ("inl"
                                                                                                               ::
                                                                                                               Data.Text.Text))))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                             _ -> coe v11
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'inr_1722
                             -> let v7 = "inr" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_808 (coe ("inr" :: Data.Text.Text))
                                             (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                             (coe d_debruijn_518 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_520 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__16
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_416
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_418
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_716
                                                       (coe d_imports_522 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_514 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_520
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__16
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_416
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_418
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_418 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C_Many_10
                                                                        -> case coe v14 of
                                                                             MAlonzo.Code.Once.Type.C__'43'__54 v15 v16
                                                                               -> let v17
                                                                                        = d__'8799'T__16
                                                                                            (coe
                                                                                               v12)
                                                                                            (coe
                                                                                               v16) in
                                                                                  coe
                                                                                    (case coe v17 of
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                         -> if coe
                                                                                                 v18
                                                                                              then coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (coe
                                                                                                        C_success_416
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                           (coe
                                                                                                              d_size_514
                                                                                                              (coe
                                                                                                                 v0)))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                           (coe
                                                                                                              d_debruijn_518
                                                                                                              (coe
                                                                                                                 v0))
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                              (coe
                                                                                                                 v12)
                                                                                                              (coe
                                                                                                                 v13)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.Type.C__'43'__54
                                                                                                                 (coe
                                                                                                                    v15)
                                                                                                                 (coe
                                                                                                                    v12)))
                                                                                                           (coe
                                                                                                              du_specInr_634))
                                                                                                        (coe
                                                                                                           (0 ::
                                                                                                              Integer))
                                                                                                        (coe
                                                                                                           d_freshCounter_520
                                                                                                           (coe
                                                                                                              v0)))
                                                                                              else coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v19)
                                                                                                     (coe
                                                                                                        C_failure_418
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                           (coe
                                                                                                              ("inr"
                                                                                                               ::
                                                                                                               Data.Text.Text))))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                             _ -> coe v11
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'arr_1724
                             -> let v7 = "arr" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_808 (coe ("arr" :: Data.Text.Text))
                                             (coe d_size_514 (coe v0)) (coe d_named_516 (coe v0))
                                             (coe d_debruijn_518 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_520 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__16
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_416
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_418
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_716
                                                       (coe d_imports_522 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_514 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_520
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__16
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_416
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_418
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_418 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v12 v13 v14
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v15 v16 v17
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> case coe v13 of
                                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                                      -> case coe
                                                                                                v14 of
                                                                                           MAlonzo.Code.Once.Type.C_Eff_58 v18 v19
                                                                                             -> let v20
                                                                                                      = d__'8799'T__16
                                                                                                          (coe
                                                                                                             v15)
                                                                                                          (coe
                                                                                                             v18) in
                                                                                                coe
                                                                                                  (let v21
                                                                                                         = d__'8799'T__16
                                                                                                             (coe
                                                                                                                v17)
                                                                                                             (coe
                                                                                                                v19) in
                                                                                                   coe
                                                                                                     (case coe
                                                                                                             v20 of
                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                          -> let v24
                                                                                                                   = coe
                                                                                                                       C_failure_418
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                          (coe
                                                                                                                             ("arr"
                                                                                                                              ::
                                                                                                                              Data.Text.Text))) in
                                                                                                             coe
                                                                                                               (case coe
                                                                                                                       v22 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                    -> case coe
                                                                                                                              v23 of
                                                                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                                                                           -> case coe
                                                                                                                                     v21 of
                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                                                  -> case coe
                                                                                                                                            v26 of
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                                         -> case coe
                                                                                                                                                   v27 of
                                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v28
                                                                                                                                                -> coe
                                                                                                                                                     C_success_416
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                                                        (coe
                                                                                                                                                           d_size_514
                                                                                                                                                           (coe
                                                                                                                                                              v0)))
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                                                                        (coe
                                                                                                                                                           d_debruijn_518
                                                                                                                                                           (coe
                                                                                                                                                              v0))
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                                                                           (coe
                                                                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                                                                              (coe
                                                                                                                                                                 v15)
                                                                                                                                                              (coe
                                                                                                                                                                 v13)
                                                                                                                                                              (coe
                                                                                                                                                                 v17))
                                                                                                                                                           (coe
                                                                                                                                                              v13)
                                                                                                                                                           (coe
                                                                                                                                                              MAlonzo.Code.Once.Type.C_Eff_58
                                                                                                                                                              (coe
                                                                                                                                                                 v15)
                                                                                                                                                              (coe
                                                                                                                                                                 v17)))
                                                                                                                                                        (coe
                                                                                                                                                           du_specArr_710))
                                                                                                                                                     (coe
                                                                                                                                                        (0 ::
                                                                                                                                                           Integer))
                                                                                                                                                     (coe
                                                                                                                                                        d_freshCounter_520
                                                                                                                                                        (coe
                                                                                                                                                           v0))
                                                                                                                                              _ -> coe
                                                                                                                                                     v24
                                                                                                                                       _ -> coe
                                                                                                                                              v24
                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                         _ -> coe
                                                                                                                                v24
                                                                                                                  _ -> coe
                                                                                                                         v24)
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                           _ -> coe
                                                                                                  v11
                                                                                    _ -> coe v11
                                                                             _ -> coe v11
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'other_1728
                             -> let v8
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased
                                          (\ v8 ->
                                             coe
                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                               (coe v1))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                             (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                v1)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                ("unit" :: Data.Text.Text))) in
                                coe
                                  (case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                       -> if coe v9
                                            then let v11
                                                       = seq
                                                           (coe v10)
                                                           (coe
                                                              C_success_392
                                                              (coe MAlonzo.Code.Once.Type.C_Unit_48)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_514 (coe v0)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
                                                              (coe (0 :: Integer))
                                                              (coe d_freshCounter_520 (coe v0))) in
                                                 coe
                                                   (case coe v11 of
                                                      C_success_392 v12 v13 v14 v15 v16
                                                        -> let v17
                                                                 = d__'8799'T__16
                                                                     (coe v2) (coe v12) in
                                                           coe
                                                             (case coe v17 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                  -> if coe v18
                                                                       then coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 C_success_416
                                                                                 (coe v13) (coe v14)
                                                                                 (coe v15)
                                                                                 (coe v16))
                                                                       else coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 C_failure_418
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                    (coe v2)
                                                                                    (coe v12)))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      C_failure_394 v12
                                                        -> let v13
                                                                 = d_lookupPoly_428
                                                                     (coe d_polys_524 (coe v0))
                                                                     (coe v1) in
                                                           coe
                                                             (case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                         -> let v17
                                                                                  = d_checkElab_1808
                                                                                      (coe
                                                                                         d_ctxWithImportsAndPolys_534
                                                                                         (coe
                                                                                            d_imports_522
                                                                                            (coe
                                                                                               v0))
                                                                                         (coe
                                                                                            d_removePoly_464
                                                                                            (coe v1)
                                                                                            (coe
                                                                                               d_polys_524
                                                                                               (coe
                                                                                                  v0))))
                                                                                      (coe v16)
                                                                                      (coe v2) in
                                                                            coe
                                                                              (case coe v17 of
                                                                                 C_success_416 v18 v19 v20 v21
                                                                                   -> coe
                                                                                        seq
                                                                                        (coe v18)
                                                                                        (coe
                                                                                           C_success_416
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                              (coe
                                                                                                 d_size_514
                                                                                                 (coe
                                                                                                    v0)))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                              (coe
                                                                                                 d_debruijn_518
                                                                                                 (coe
                                                                                                    v0))
                                                                                              (coe
                                                                                                 v2)
                                                                                              (coe
                                                                                                 v19))
                                                                                           (coe v20)
                                                                                           (coe
                                                                                              v21))
                                                                                 C_failure_418 v18
                                                                                   -> coe v17
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe C_failure_418 (coe v12)
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            else (let v11
                                                        = seq
                                                            (coe v10)
                                                            (let v11
                                                                   = coe
                                                                       du_go_808 (coe v1)
                                                                       (coe d_size_514 (coe v0))
                                                                       (coe d_named_516 (coe v0))
                                                                       (coe
                                                                          d_debruijn_518
                                                                          (coe v0)) in
                                                             coe
                                                               (case coe v11 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                    -> case coe v12 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> coe
                                                                                       C_success_392
                                                                                       (coe v13)
                                                                                       (coe v15)
                                                                                       (coe v16)
                                                                                       (coe
                                                                                          (0 ::
                                                                                             Integer))
                                                                                       (coe
                                                                                          d_freshCounter_520
                                                                                          (coe v0))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> let v12
                                                                             = d_lookupImport_716
                                                                                 (coe
                                                                                    d_imports_522
                                                                                    (coe v0))
                                                                                 (coe v1) in
                                                                       coe
                                                                         (case coe v12 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                              -> coe
                                                                                   C_success_392
                                                                                   (coe v13)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                      (coe
                                                                                         d_size_514
                                                                                         (coe v0)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_prim_494
                                                                                      v1)
                                                                                   (coe
                                                                                      (0 ::
                                                                                         Integer))
                                                                                   (coe
                                                                                      d_freshCounter_520
                                                                                      (coe v0))
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> coe
                                                                                   C_failure_394
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                                      (coe v1))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                  coe
                                                    (case coe v11 of
                                                       C_success_392 v12 v13 v14 v15 v16
                                                         -> let v17
                                                                  = d__'8799'T__16
                                                                      (coe v2) (coe v12) in
                                                            coe
                                                              (case coe v17 of
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                   -> if coe v18
                                                                        then coe
                                                                               seq (coe v19)
                                                                               (coe
                                                                                  C_success_416
                                                                                  (coe v13)
                                                                                  (coe v14)
                                                                                  (coe v15)
                                                                                  (coe v16))
                                                                        else coe
                                                                               seq (coe v19)
                                                                               (coe
                                                                                  C_failure_418
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                     (coe v2)
                                                                                     (coe v12)))
                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                       C_failure_394 v12
                                                         -> let v13
                                                                  = d_lookupPoly_428
                                                                      (coe d_polys_524 (coe v0))
                                                                      (coe v1) in
                                                            coe
                                                              (case coe v13 of
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                   -> case coe v14 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                          -> let v17
                                                                                   = d_checkElab_1808
                                                                                       (coe
                                                                                          d_ctxWithImportsAndPolys_534
                                                                                          (coe
                                                                                             d_imports_522
                                                                                             (coe
                                                                                                v0))
                                                                                          (coe
                                                                                             d_removePoly_464
                                                                                             (coe
                                                                                                v1)
                                                                                             (coe
                                                                                                d_polys_524
                                                                                                (coe
                                                                                                   v0))))
                                                                                       (coe v16)
                                                                                       (coe v2) in
                                                                             coe
                                                                               (case coe v17 of
                                                                                  C_success_416 v18 v19 v20 v21
                                                                                    -> coe
                                                                                         seq
                                                                                         (coe v18)
                                                                                         (coe
                                                                                            C_success_416
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                               (coe
                                                                                                  d_size_514
                                                                                                  (coe
                                                                                                     v0)))
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                               (coe
                                                                                                  d_debruijn_518
                                                                                                  (coe
                                                                                                     v0))
                                                                                               (coe
                                                                                                  v2)
                                                                                               (coe
                                                                                                  v19))
                                                                                            (coe
                                                                                               v20)
                                                                                            (coe
                                                                                               v21))
                                                                                  C_failure_418 v18
                                                                                    -> coe v17
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                   -> coe C_failure_418 (coe v12)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkPair
d_checkPair_1826 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
d_checkPair_1826 v0 v1 v2 v3
  = let v4
          = coe
              C_failure_418
              (coe
                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                 (coe ("pair" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v7
                  -> case coe v7 of
                       l | (==) l ("pair" :: Data.Text.Text) ->
                           case coe v3 of
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v8 v9 v10
                               -> case coe v9 of
                                    MAlonzo.Code.Once.Type.C_Many_10
                                      -> case coe v10 of
                                           MAlonzo.Code.Once.Type.C__'42'__52 v11 v12
                                             -> let v13
                                                      = d_checkElab_1808
                                                          (coe v0) (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                             (coe v8) (coe v9) (coe v11)) in
                                                coe
                                                  (case coe v13 of
                                                     C_success_416 v14 v15 v16 v17
                                                       -> let v18
                                                                = d_checkElab_1808
                                                                    (coe v0) (coe v2)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                       (coe v8) (coe v9)
                                                                       (coe v12)) in
                                                          coe
                                                            (case coe v18 of
                                                               C_success_416 v19 v20 v21 v22
                                                                 -> coe
                                                                      C_success_416
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                            (coe
                                                                               MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                               (coe
                                                                                  d_size_514
                                                                                  (coe v0)))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                               (coe v9) (coe v14)))
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                            (coe v9) (coe v19)))
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                            (coe
                                                                               MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                               (coe
                                                                                  d_size_514
                                                                                  (coe v0)))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                               (coe v9) (coe v14)))
                                                                         v19
                                                                         (MAlonzo.Code.Once.Type.d__'8658'__78
                                                                            (coe v8) (coe v12))
                                                                         v9
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                            (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                               (coe
                                                                                  d_size_514
                                                                                  (coe v0)))
                                                                            v14
                                                                            (MAlonzo.Code.Once.Type.d__'8658'__78
                                                                               (coe v8) (coe v11))
                                                                            v9
                                                                            (coe
                                                                               MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                               (coe
                                                                                  d_debruijn_518
                                                                                  (coe v0))
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                     (coe v8)
                                                                                     (coe v11))
                                                                                  (coe v9)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                        (coe v8)
                                                                                        (coe v12))
                                                                                     (coe v9)
                                                                                     (coe v3)))
                                                                               (coe
                                                                                  du_specPair_648
                                                                                  (coe v8)))
                                                                            v15)
                                                                         v20)
                                                                      (coe
                                                                         addInt (coe (1 :: Integer))
                                                                         (coe
                                                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                            (coe v16) (coe v21)))
                                                                      (coe v22)
                                                               C_failure_418 v19 -> coe v18
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     C_failure_418 v14 -> coe v13
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> coe v4
                                    _ -> coe v4
                             _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkCompose
d_checkCompose_1836 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
d_checkCompose_1836 v0 v1 v2 v3
  = let v4
          = coe
              C_failure_418
              (coe
                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                 (coe ("compose" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v7
                  -> case coe v7 of
                       l | (==) l ("compose" :: Data.Text.Text) ->
                           case coe v3 of
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v8 v9 v10
                               -> case coe v9 of
                                    MAlonzo.Code.Once.Type.C_Many_10
                                      -> let v11 = d_inferElab_1802 (coe v0) (coe v2) in
                                         coe
                                           (case coe v11 of
                                              C_success_392 v12 v13 v14 v15 v16
                                                -> case coe v12 of
                                                     MAlonzo.Code.Once.Type.C_Unit_48
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C_Void_50
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C__'42'__52 v17 v18
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C__'43'__54 v17 v18
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v17 v18 v19
                                                       -> case coe v18 of
                                                            MAlonzo.Code.Once.Type.C_Zero_6
                                                              -> coe
                                                                   C_failure_418
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                      (coe
                                                                         ("compose"
                                                                          ::
                                                                          Data.Text.Text)))
                                                            MAlonzo.Code.Once.Type.C_One_8
                                                              -> coe
                                                                   C_failure_418
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                      (coe
                                                                         ("compose"
                                                                          ::
                                                                          Data.Text.Text)))
                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                              -> let v20
                                                                       = d__'8799'T__16
                                                                           (coe v8) (coe v17) in
                                                                 coe
                                                                   (case coe v20 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                        -> if coe v21
                                                                             then coe
                                                                                    seq (coe v22)
                                                                                    (let v23
                                                                                           = d_checkElab_1808
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  v6)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     v18)
                                                                                                  (coe
                                                                                                     v10)) in
                                                                                     coe
                                                                                       (case coe
                                                                                               v23 of
                                                                                          C_success_416 v24 v25 v26 v27
                                                                                            -> coe
                                                                                                 C_success_416
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_514
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                          (coe
                                                                                                             v18)
                                                                                                          (coe
                                                                                                             v24)))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                       (coe
                                                                                                          v18)
                                                                                                       (coe
                                                                                                          v13)))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_514
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                          (coe
                                                                                                             v18)
                                                                                                          (coe
                                                                                                             v24)))
                                                                                                    v13
                                                                                                    (MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                                       (coe
                                                                                                          v17)
                                                                                                       (coe
                                                                                                          v19))
                                                                                                    v18
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                                       (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_514
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       v24
                                                                                                       (MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                                          (coe
                                                                                                             v19)
                                                                                                          (coe
                                                                                                             v10))
                                                                                                       v18
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                                          (coe
                                                                                                             d_debruijn_518
                                                                                                             (coe
                                                                                                                v0))
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                                                (coe
                                                                                                                   v19)
                                                                                                                (coe
                                                                                                                   v10))
                                                                                                             (coe
                                                                                                                v18)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                                                   (coe
                                                                                                                      v17)
                                                                                                                   (coe
                                                                                                                      v19))
                                                                                                                (coe
                                                                                                                   v18)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                                   (coe
                                                                                                                      v17)
                                                                                                                   (coe
                                                                                                                      v18)
                                                                                                                   (coe
                                                                                                                      v10))))
                                                                                                          (coe
                                                                                                             du_specCompose_698
                                                                                                             (coe
                                                                                                                v17)
                                                                                                             (coe
                                                                                                                v19)))
                                                                                                       v25)
                                                                                                    v14)
                                                                                                 (coe
                                                                                                    addInt
                                                                                                    (coe
                                                                                                       (1 ::
                                                                                                          Integer))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                       (coe
                                                                                                          v26)
                                                                                                       (coe
                                                                                                          v15)))
                                                                                                 (coe
                                                                                                    v27)
                                                                                          C_failure_418 v24
                                                                                            -> coe
                                                                                                 v23
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                             else coe
                                                                                    seq (coe v22)
                                                                                    (coe
                                                                                       C_failure_418
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                          (coe
                                                                                             ("compose"
                                                                                              ::
                                                                                              Data.Text.Text))))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     MAlonzo.Code.Once.Type.C_Eff_58 v17 v18
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C_μ'45'type_60 v17
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C_ν'45'type_62 v17
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C_Int_64
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C_Float_66
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C_Str_68
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     MAlonzo.Code.Once.Type.C_Buffer_70
                                                       -> coe
                                                            C_failure_418
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                               (coe ("compose" :: Data.Text.Text)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              C_failure_394 v12
                                                -> let v13
                                                         = d_composeArgB_1668
                                                             (coe v0) (coe v2) (coe v8) in
                                                   coe
                                                     (case coe v13 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                          -> let v15
                                                                   = d_checkElab_1808
                                                                       (coe v0) (coe v2)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                          (coe v8) (coe v9)
                                                                          (coe v14)) in
                                                             coe
                                                               (case coe v15 of
                                                                  C_success_416 v16 v17 v18 v19
                                                                    -> let v20
                                                                             = d_checkElab_1808
                                                                                 (coe v0) (coe v6)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                    (coe v14)
                                                                                    (coe v9)
                                                                                    (coe v10)) in
                                                                       coe
                                                                         (case coe v20 of
                                                                            C_success_416 v21 v22 v23 v24
                                                                              -> coe
                                                                                   C_success_416
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                            (coe
                                                                                               d_size_514
                                                                                               (coe
                                                                                                  v0)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                            (coe v9)
                                                                                            (coe
                                                                                               v21)))
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                         (coe v9)
                                                                                         (coe v16)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                            (coe
                                                                                               d_size_514
                                                                                               (coe
                                                                                                  v0)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                            (coe v9)
                                                                                            (coe
                                                                                               v21)))
                                                                                      v16
                                                                                      (MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                         (coe v8)
                                                                                         (coe v14))
                                                                                      v9
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                         (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                            (coe
                                                                                               d_size_514
                                                                                               (coe
                                                                                                  v0)))
                                                                                         v21
                                                                                         (MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                            (coe
                                                                                               v14)
                                                                                            (coe
                                                                                               v10))
                                                                                         v9
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                                            (coe
                                                                                               d_debruijn_518
                                                                                               (coe
                                                                                                  v0))
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                                  (coe
                                                                                                     v14)
                                                                                                  (coe
                                                                                                     v10))
                                                                                               (coe
                                                                                                  v9)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                                     (coe
                                                                                                        v8)
                                                                                                     (coe
                                                                                                        v14))
                                                                                                  (coe
                                                                                                     v9)
                                                                                                  (coe
                                                                                                     v3)))
                                                                                            (coe
                                                                                               du_specCompose_698
                                                                                               (coe
                                                                                                  v8)
                                                                                               (coe
                                                                                                  v14)))
                                                                                         v22)
                                                                                      v17)
                                                                                   (coe
                                                                                      addInt
                                                                                      (coe
                                                                                         (1 ::
                                                                                            Integer))
                                                                                      (coe
                                                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                         (coe v23)
                                                                                         (coe v18)))
                                                                                   (coe v24)
                                                                            C_failure_418 v21
                                                                              -> coe v20
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  C_failure_418 v16 -> coe v15
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> coe
                                                               C_failure_418
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                  (coe
                                                                     ("compose" :: Data.Text.Text)))
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> coe v4
                             _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkCurry
d_checkCurry_1844 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
d_checkCurry_1844 v0 v1 v2
  = let v3
          = coe
              C_failure_418
              (coe
                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                 (coe ("curry" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v4 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Type.C_Many_10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v7 v8 v9
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> let v10
                                         = d_checkElab_1808
                                             (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'42'__52 (coe v4)
                                                   (coe v7))
                                                (coe v8) (coe v9)) in
                                   coe
                                     (case coe v10 of
                                        C_success_416 v11 v12 v13 v14
                                          -> coe
                                               C_success_416
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                     (coe d_size_514 (coe v0)))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                     (coe v8) (coe v11)))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                  (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                     (coe d_size_514 (coe v0)))
                                                  v11
                                                  (MAlonzo.Code.Once.Type.d__'8658'__78
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'42'__52 (coe v4)
                                                        (coe v7))
                                                     (coe v9))
                                                  v8
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                     (coe d_debruijn_518 (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                        (coe
                                                           MAlonzo.Code.Once.Type.d__'8658'__78
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'42'__52
                                                              (coe v4) (coe v7))
                                                           (coe v9))
                                                        (coe v8)
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                           (coe v4) (coe v8) (coe v6)))
                                                     (coe du_specCurry_674 (coe v4) (coe v7)))
                                                  v12)
                                               (coe addInt (coe (1 :: Integer)) (coe v13)) (coe v14)
                                        C_failure_418 v11 -> coe v10
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v3
                       _ -> coe v3
                _ -> coe v3
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkApply
d_checkApply_1852 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> T_CheckElabResult_402
d_checkApply_1852 v0 v1 v2
  = let v3 = d_inferElab_1802 (coe v0) (coe v1) in
    coe
      (case coe v3 of
         C_success_392 v4 v5 v6 v7 v8
           -> case coe v4 of
                MAlonzo.Code.Once.Type.C__'42'__52 v9 v10
                  -> case coe v9 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v11 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> let v14 = d__'8799'T__16 (coe v11) (coe v10) in
                                   coe
                                     (case coe v14 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                          -> if coe v15
                                               then let v17
                                                          = seq
                                                              (coe v16)
                                                              (coe
                                                                 C_success_392 (coe v13)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                    (coe
                                                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                       (coe d_size_514 (coe v0)))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                       (coe v12) (coe v5)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                    (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                       (coe d_size_514 (coe v0)))
                                                                    v5
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C__'42'__52
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.d__'8658'__78
                                                                          (coe v11) (coe v13))
                                                                       (coe v11))
                                                                    v12
                                                                    (coe
                                                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                                       (coe d_debruijn_518 (coe v0))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                          (coe
                                                                             MAlonzo.Code.Once.Type.C__'42'__52
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d__'8658'__78
                                                                                (coe v11) (coe v13))
                                                                             (coe v11))
                                                                          (coe v12) (coe v13))
                                                                       (coe
                                                                          d_specApply_686 (coe v11)
                                                                          (coe v13)))
                                                                    v6)
                                                                 (coe
                                                                    addInt (coe (1 :: Integer))
                                                                    (coe v7))
                                                                 (coe v8)) in
                                                    coe
                                                      (case coe v17 of
                                                         C_success_392 v18 v19 v20 v21 v22
                                                           -> let v23
                                                                    = d__'8799'T__16
                                                                        (coe v2) (coe v18) in
                                                              coe
                                                                (case coe v23 of
                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                     -> if coe v24
                                                                          then coe
                                                                                 seq (coe v25)
                                                                                 (coe
                                                                                    C_success_416
                                                                                    (coe v19)
                                                                                    (coe v20)
                                                                                    (coe v21)
                                                                                    (coe v22))
                                                                          else coe
                                                                                 seq (coe v25)
                                                                                 (coe
                                                                                    C_failure_418
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                       (coe v2)
                                                                                       (coe v18)))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         C_failure_394 v18
                                                           -> coe C_failure_418 (coe v18)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               else (let v17
                                                           = seq
                                                               (coe v16)
                                                               (coe
                                                                  C_failure_394
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                     (coe
                                                                        ("apply"
                                                                         ::
                                                                         Data.Text.Text)))) in
                                                     coe
                                                       (case coe v17 of
                                                          C_success_392 v18 v19 v20 v21 v22
                                                            -> let v23
                                                                     = d__'8799'T__16
                                                                         (coe v2) (coe v18) in
                                                               coe
                                                                 (case coe v23 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                      -> if coe v24
                                                                           then coe
                                                                                  seq (coe v25)
                                                                                  (coe
                                                                                     C_success_416
                                                                                     (coe v19)
                                                                                     (coe v20)
                                                                                     (coe v21)
                                                                                     (coe v22))
                                                                           else coe
                                                                                  seq (coe v25)
                                                                                  (coe
                                                                                     C_failure_418
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                        (coe v2)
                                                                                        (coe v18)))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          C_failure_394 v18
                                                            -> coe C_failure_418 (coe v18)
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe (coe C_failure_418 (coe v14))
                       _ -> let v11
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                      (coe ("apply" :: Data.Text.Text)) in
                            coe (coe C_failure_418 (coe v11))
                _ -> let v9
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                               (coe ("apply" :: Data.Text.Text)) in
                     coe (coe C_failure_418 (coe v9))
         C_failure_394 v4
           -> case coe v3 of
                C_success_392 v5 v6 v7 v8 v9
                  -> let v10 = d__'8799'T__16 (coe v2) (coe v5) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                            -> if coe v11
                                 then coe
                                        seq (coe v12)
                                        (coe C_success_416 (coe v6) (coe v7) (coe v8) (coe v9))
                                 else coe
                                        seq (coe v12)
                                        (coe
                                           C_failure_418
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                              (coe v2) (coe v5)))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_394 v5 -> coe C_failure_418 (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate._.mkArith
d_mkArith_3130 ::
  T_NamedCtx_500 ->
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
d_mkArith_3130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               ~v12 v13 v14 v15
  = du_mkArith_3130 v13 v14 v15
du_mkArith_3130 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_mkArith_3130 v0 v1 v2
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
d_mkCmp_3138 ::
  T_NamedCtx_500 ->
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
d_mkCmp_3138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             v13 v14 v15
  = du_mkCmp_3138 v13 v14 v15
du_mkCmp_3138 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_mkCmp_3138 v0 v1 v2
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
d_checkElab'45'fallback'45'RInt_5554 ::
  T_NamedCtx_500 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RInt_5554 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_int_350 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_520 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RStringLit
d_checkElab'45'fallback'45'RStringLit_5584 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RStringLit_5584 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_str_356 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_520 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RUnit
d_checkElab'45'fallback'45'RUnit_5612 ::
  T_NamedCtx_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnit_5612 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_520 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RQualified
d_checkElab'45'fallback'45'RQualified_5648 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RQualified_5648 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
                                           v7 ~v8
  = du_checkElab'45'fallback'45'RQualified_5648 v3 v5 v6 v7
du_checkElab'45'fallback'45'RQualified_5648 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RQualified_5648 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RAnnot_5704 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RAnnot_5704 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
  = du_checkElab'45'fallback'45'RAnnot_5704 v2 v4 v5 v6
du_checkElab'45'fallback'45'RAnnot_5704 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RAnnot_5704 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RPair_5756 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RPair_5756 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
                                      ~v8
  = du_checkElab'45'fallback'45'RPair_5756 v3 v5 v6 v7
du_checkElab'45'fallback'45'RPair_5756 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RPair_5756 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RLet_5816 ::
  T_NamedCtx_500 ->
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
d_checkElab'45'fallback'45'RLet_5816 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7
                                     v8 ~v9
  = du_checkElab'45'fallback'45'RLet_5816 v4 v6 v7 v8
du_checkElab'45'fallback'45'RLet_5816 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RLet_5816 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RDestruct_5886 ::
  T_NamedCtx_500 ->
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
d_checkElab'45'fallback'45'RDestruct_5886 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                          v6 ~v7 v8 v9 v10 ~v11
  = du_checkElab'45'fallback'45'RDestruct_5886 v6 v8 v9 v10
du_checkElab'45'fallback'45'RDestruct_5886 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RDestruct_5886 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RUnaryOp_5962 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_UnaryOp_30 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp_5962 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
                                         v7 ~v8
  = du_checkElab'45'fallback'45'RUnaryOp_5962 v3 v5 v6 v7
du_checkElab'45'fallback'45'RUnaryOp_5962 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp_5962 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RVar'45'unit_6006 ::
  T_NamedCtx_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'unit_6006 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_520 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-id
d_checkElab'45'fallback'45'RVar'45'id_6030 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'id_6030 v0 v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'id_6030 v0 v1
du_checkElab'45'fallback'45'RVar'45'id_6030 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'id_6030 v0 v1
  = let v2 = d__'8799'T__16 (coe v1) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                             (coe d_debruijn_518 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v1)
                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
                             (coe du_specId_596))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_520 (coe v0)) erased)))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-fst
d_checkElab'45'fallback'45'RVar'45'fst_6082 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'fst_6082 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'fst_6082 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'fst_6082 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'fst_6082 v0 v1 v2
  = let v3 = d__'8799'T__16 (coe v1) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                             (coe d_debruijn_518 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v1) (coe v2))
                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
                             (coe du_specFst_604 (coe v2)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_520 (coe v0)) erased)))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-snd
d_checkElab'45'fallback'45'RVar'45'snd_6140 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'snd_6140 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'snd_6140 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'snd_6140 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'snd_6140 v0 v1 v2
  = let v3 = d__'8799'T__16 (coe v2) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                             (coe d_debruijn_518 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v1) (coe v2))
                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                             (coe du_specSnd_614 (coe v1)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_520 (coe v0)) erased)))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-terminal
d_checkElab'45'fallback'45'RVar'45'terminal_6196 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminal_6196 v0 v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'terminal_6196 v0 v1
du_checkElab'45'fallback'45'RVar'45'terminal_6196 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminal_6196 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
         (coe d_debruijn_518 (coe v0))
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v1)
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_Unit_48))
         (coe du_specTerminal_658))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_520 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-initial
d_checkElab'45'fallback'45'RVar'45'initial_6224 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'initial_6224 v0 v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'initial_6224 v0 v1
du_checkElab'45'fallback'45'RVar'45'initial_6224 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'initial_6224 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
         (coe d_debruijn_518 (coe v0))
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
            (coe MAlonzo.Code.Once.Type.C_Void_50)
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
         (coe du_specInitial_664))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_520 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-inl
d_checkElab'45'fallback'45'RVar'45'inl_6254 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inl_6254 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'inl_6254 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'inl_6254 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inl_6254 v0 v1 v2
  = let v3 = d__'8799'T__16 (coe v1) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                             (coe d_debruijn_518 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v1)
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C__'43'__54 (coe v1) (coe v2)))
                             (coe du_specInl_624))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_520 (coe v0)) erased)))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-inr
d_checkElab'45'fallback'45'RVar'45'inr_6312 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inr_6312 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'inr_6312 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'inr_6312 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inr_6312 v0 v1 v2
  = let v3 = d__'8799'T__16 (coe v2) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                             (coe d_debruijn_518 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v2)
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C__'43'__54 (coe v1) (coe v2)))
                             (coe du_specInr_634))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_520 (coe v0)) erased)))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-arr
d_checkElab'45'fallback'45'RVar'45'arr_6370 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'arr_6370 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'arr_6370 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'arr_6370 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'arr_6370 v0 v1 v2
  = let v3 = d__'8799'T__16 (coe v1) (coe v1) in
    coe
      (let v4 = d__'8799'T__16 (coe v2) (coe v2) in
       coe
         (let v5
                = case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                      -> coe
                           seq (coe v5)
                           (coe
                              seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                    _ -> MAlonzo.RTE.mazUnreachableError in
          coe
            (case coe v3 of
               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                 -> let v8
                          = case coe v4 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                       -> case coe v9 of
                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                              -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError in
                    coe
                      (if coe v6
                         then case coe v7 of
                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                  -> case coe v4 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                         -> case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                -> case coe v11 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                       -> coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                               (coe d_debruijn_518 (coe v0))
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                     (coe v1)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_Many_10)
                                                                     (coe v2))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C_Eff_58
                                                                     (coe v1) (coe v2)))
                                                               (coe du_specArr_710))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe (0 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe d_freshCounter_520 (coe v0))
                                                                  erased))
                                                     _ -> coe v8
                                              _ -> coe v8
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> coe v8
                         else (case coe v7 of
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                   -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                 _ -> coe v8))
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-pair
d_checkElab'45'fallback'45'RApp'45'pair_6462 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'pair_6462 v0 ~v1 ~v2 v3 v4 v5 v6
                                             v7 v8 v9 v10 ~v11 v12 v13 ~v14 ~v15
  = du_checkElab'45'fallback'45'RApp'45'pair_6462
      v0 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13
du_checkElab'45'fallback'45'RApp'45'pair_6462 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'pair_6462 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8 v9 v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_214
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
            (coe
               MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
               (coe d_size_514 (coe v0)))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4)))
         v5 (MAlonzo.Code.Once.Type.d__'8658'__78 (coe v1) (coe v3))
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_app_214
            (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
               (coe d_size_514 (coe v0)))
            v4 (MAlonzo.Code.Once.Type.d__'8658'__78 (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
               (coe d_debruijn_518 (coe v0))
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                  (coe MAlonzo.Code.Once.Type.d__'8658'__78 (coe v1) (coe v2))
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                     (coe MAlonzo.Code.Once.Type.d__'8658'__78 (coe v1) (coe v3))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v2) (coe v3)))))
               (coe du_specPair_648 (coe v1)))
            v6)
         v7)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            addInt (coe (1 :: Integer))
            (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v9)))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-compose
d_checkElab'45'fallback'45'RApp'45'compose_6522 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'compose_6522 v0 ~v1 ~v2 v3 v4 v5
                                                v6 v7 v8 v9 v10 v11 v12 ~v13 ~v14 ~v15
  = du_checkElab'45'fallback'45'RApp'45'compose_6522
      v0 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_checkElab'45'fallback'45'RApp'45'compose_6522 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'compose_6522 v0 v1 v2 v3 v4 v5
                                                 v6 v7 v8 v9 v10
  = let v11 = d__'8799'T__16 (coe v1) (coe v1) in
    coe
      (case coe v11 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
           -> if coe v12
                then coe
                       seq (coe v13)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_app_214
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                   (coe d_size_514 (coe v0)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4)))
                             v5 (MAlonzo.Code.Once.Type.d__'8658'__78 (coe v1) (coe v2))
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                   (coe d_size_514 (coe v0)))
                                v4 (MAlonzo.Code.Once.Type.d__'8658'__78 (coe v2) (coe v3))
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe
                                   MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                   (coe d_debruijn_518 (coe v0))
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                      (coe MAlonzo.Code.Once.Type.d__'8658'__78 (coe v2) (coe v3))
                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                         (coe
                                            MAlonzo.Code.Once.Type.d__'8658'__78 (coe v1) (coe v2))
                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v1)
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))))
                                   (coe du_specCompose_698 (coe v1) (coe v2)))
                                v6)
                             v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                addInt (coe (1 :: Integer))
                                (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v10)))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased)))
                else coe
                       seq (coe v13) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-curry
d_checkElab'45'fallback'45'RApp'45'curry_6610 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'curry_6610 v0 ~v1 v2 v3 v4 v5 v6
                                              v7 v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'curry_6610
      v0 v2 v3 v4 v5 v6 v7 v8
du_checkElab'45'fallback'45'RApp'45'curry_6610 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'curry_6610 v0 v1 v2 v3 v4 v5 v6
                                               v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_214
         (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
            (coe d_size_514 (coe v0)))
         v4
         (MAlonzo.Code.Once.Type.d__'8658'__78
            (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v1) (coe v2))
            (coe v3))
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe
            MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
            (coe d_debruijn_518 (coe v0))
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
               (coe
                  MAlonzo.Code.Once.Type.d__'8658'__78
                  (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v1) (coe v2))
                  (coe v3))
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v1)
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 (coe v2)
                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))))
            (coe du_specCurry_674 (coe v1) (coe v2)))
         v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (1 :: Integer)) (coe v6))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-apply
d_checkElab'45'fallback'45'RApp'45'apply_6650 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply_6650 v0 ~v1 v2 v3 v4 v5 v6
                                              v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'apply_6650
      v0 v2 v3 v4 v5 v6 v7
du_checkElab'45'fallback'45'RApp'45'apply_6650 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply_6650 v0 v1 v2 v3 v4 v5 v6
  = let v7 = d__'8799'T__16 (coe v1) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe
                       seq (coe v9)
                       (let v10 = d__'8799'T__16 (coe v2) (coe v2) in
                        coe
                          (case coe v10 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                               -> if coe v11
                                    then coe
                                           seq (coe v12)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                 (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                    (coe d_size_514 (coe v0)))
                                                 v3
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'42'__52
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                       (coe v1)
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe v2))
                                                    (coe v1))
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                                                    (coe d_debruijn_518 (coe v0))
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C__'42'__52
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                             (coe v1)
                                                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                             (coe v2))
                                                          (coe v1))
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe v2))
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lam_198
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe
                                                          MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                                                             (coe MAlonzo.Code.Once.Type.C_One_8)
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                                                             (coe MAlonzo.Code.Once.Type.C_One_8)
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))
                                                          v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fst''_254
                                                             v1
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_var_182
                                                                (coe
                                                                   MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_snd''_266
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
                                                                (coe v1)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                (coe v2))
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_var_182
                                                                (coe
                                                                   MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
                                                 v4)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe addInt (coe (1 :: Integer)) (coe v5))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v6) erased)))
                                    else coe
                                           seq (coe v12)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                else coe
                       seq (coe v9) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-poly
d_checkElab'45'fallback'45'RVar'45'poly_6740 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_PolyType_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly_6740 v0 v1 v2 ~v3 ~v4 v5 v6
                                             v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_checkElab'45'fallback'45'RVar'45'poly_6740 v0 v1 v2 v5 v6 v7
du_checkElab'45'fallback'45'RVar'45'poly_6740 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly_6740 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v6 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                 (coe ("unit" :: Data.Text.Text))) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe
                       seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                else coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1084
                             (coe d_debruijn_518 (coe v0)) (coe v2) (coe v3))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-id
d_checkElab'45'fallback'45'RApp'45'id_6842 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id_6842 ~v0 ~v1 v2 ~v3 v4 v5 v6
                                           ~v7
  = du_checkElab'45'fallback'45'RApp'45'id_6842 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'id_6842 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id_6842 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RApp'45'fst_6892 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst_6892 ~v0 ~v1 v2 ~v3 v4 v5 v6
                                            ~v7
  = du_checkElab'45'fallback'45'RApp'45'fst_6892 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'fst_6892 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst_6892 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RApp'45'snd_6942 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd_6942 ~v0 ~v1 v2 ~v3 v4 v5 v6
                                            ~v7
  = du_checkElab'45'fallback'45'RApp'45'snd_6942 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'snd_6942 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd_6942 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RApp'45'generic_6994 ::
  T_NamedCtx_500 ->
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
d_checkElab'45'fallback'45'RApp'45'generic_6994 ~v0 ~v1 ~v2 v3 ~v4
                                                v5 v6 v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'generic_6994 v3 v5 v6 v7
du_checkElab'45'fallback'45'RApp'45'generic_6994 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic_6994 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RApp'45'terminal_7064 ::
  T_NamedCtx_500 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'terminal_7064 ~v0 ~v1 v2 ~v3 v4
                                                 v5 v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'terminal_7064 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'terminal_7064 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'terminal_7064 v0 v1 v2 v3
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
d_checkElab'45'fallback'45'RBinOp_7118 ::
  T_NamedCtx_500 ->
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
d_checkElab'45'fallback'45'RBinOp_7118 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7
                                       v8 ~v9
  = du_checkElab'45'fallback'45'RBinOp_7118 v4 v6 v7 v8
du_checkElab'45'fallback'45'RBinOp_7118 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RBinOp_7118 v0 v1 v2 v3
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
d_compileExprTyped_7162 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_12
d_compileExprTyped_7162 v0 v1
  = let v2
          = d_checkElab_1808 (coe d_emptyCtx_528) (coe v0) (coe v1) in
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
d_compileExpr_7186 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_7186 v0
  = let v1 = d_inferElab_1802 (coe d_emptyCtx_528) (coe v0) in
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
