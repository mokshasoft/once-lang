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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Postulates
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.PolySyntax
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Elaborate.weakenFromEmpty
d_weakenFromEmpty_12 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_weakenFromEmpty_12 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8 -> coe v3
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v5 v6 v7
        -> let v8 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v9
                    = coe
                        MAlonzo.Code.Once.Postulates.d_coerceQuantity_30 v8 v5 v6 v2 v7 v7
                        (coe
                           MAlonzo.Code.Once.Surface.Thinning.du_weaken_476 v5 v6 v2 v7
                           (d_weakenFromEmpty_12 (coe v8) (coe v5) (coe v2) (coe v3))) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Once.Type.C_Many_10
                     -> coe
                          MAlonzo.Code.Once.Surface.Thinning.du_weaken_476 v5 v6 v2 v7
                          (d_weakenFromEmpty_12 (coe v8) (coe v5) (coe v2) (coe v3))
                   _ -> coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._≟F_
d__'8799'F__34
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate._\8799F_"
-- Once.TypeCheck.Elaborate._≟T_
d__'8799'T__40 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'T__40 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_44
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Void_46
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'42'__48 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'42'__48 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v4 v5
               -> let v6 = d__'8799'T__40 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__40 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C__'43'__50 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__50 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v4 v5
               -> let v6 = d__'8799'T__40 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__40 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v5 v6 v7
               -> let v8 = d__'8799'T__40 (coe v2) (coe v5) in
                  coe
                    (let v9
                           = MAlonzo.Code.Once.Type.d__'8799'q__26 (coe v3) (coe v6) in
                     coe
                       (let v10 = d__'8799'T__40 (coe v4) (coe v7) in
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
             MAlonzo.Code.Once.Type.C_Eff_54 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v4 v5
               -> let v6 = d__'8799'T__40 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__40 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_56 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v3
               -> let v4 = coe d__'8799'F__34 v2 v3 in
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
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_ν'45'type_58 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v3
               -> let v4 = coe d__'8799'F__34 v2 v3 in
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
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_60
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Float_62
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Str_64
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Buffer_66
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__48 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__50 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._≟PF_
d__'8799'PF__294
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate._\8799PF_"
-- Once.TypeCheck.Elaborate._≟PT_
d__'8799'PT__300 ::
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'PT__300 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PUnit_80
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PVoid_82
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__P'42'__84 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'42'__84 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v4 v5
               -> let v6 = d__'8799'PT__300 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'PT__300 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C__P'43'__86 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'43'__86 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v4 v5
               -> let v6 = d__'8799'PT__300 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'PT__300 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v5 v6 v7
               -> let v8 = d__'8799'PT__300 (coe v2) (coe v5) in
                  coe
                    (let v9 = d__'8799'PT__300 (coe v4) (coe v7) in
                     coe
                       (let v10
                              = MAlonzo.Code.Once.Type.d__'8799'q__26 (coe v3) (coe v6) in
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
             MAlonzo.Code.Once.Type.C_PEff_90 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PEff_90 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v4 v5
               -> let v6 = d__'8799'PT__300 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'PT__300 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v3
               -> let v4 = coe d__'8799'PF__294 v2 v3 in
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
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Pν'45'type_94 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v3
               -> let v4 = coe d__'8799'PF__294 v2 v3 in
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
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PInt_96
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PFloat_98
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PStr_100
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PBuffer_102
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_TVar_104 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_TVar_104 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'42'__84 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'43'__86 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PEff_90 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_104 v3
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
-- Once.TypeCheck.Elaborate.matchesPolyType
d_matchesPolyType_570 ::
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_70
d_matchesPolyType_570 v0 v1
  = let v2
          = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
            coe
              (case coe v1 of
                 MAlonzo.Code.Once.Type.C_TVar_104 v3
                   -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                 _ -> coe v2) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_PUnit_80
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PUnit_80
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_TVar_104 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_PVoid_82
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PVoid_82
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_TVar_104 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__P'42'__84 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__P'42'__84 v5 v6
                  -> let v7 = d_matchesPolyType_570 (coe v3) (coe v5) in
                     coe
                       (let v8 = d_matchesPolyType_570 (coe v4) (coe v6) in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.Type.C__P'42'__84 (coe v9)
                                              (coe v10))
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                MAlonzo.Code.Once.Type.C_TVar_104 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__P'43'__86 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__P'43'__86 v5 v6
                  -> let v7 = d_matchesPolyType_570 (coe v3) (coe v5) in
                     coe
                       (let v8 = d_matchesPolyType_570 (coe v4) (coe v6) in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.Type.C__P'43'__86 (coe v9)
                                              (coe v10))
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                MAlonzo.Code.Once.Type.C_TVar_104 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v3 v4 v5
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v6 v7 v8
                  -> let v9 = d_matchesPolyType_570 (coe v3) (coe v6) in
                     coe
                       (let v10 = d_matchesPolyType_570 (coe v5) (coe v8) in
                        coe
                          (case coe v9 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                               -> case coe v10 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88
                                              (coe v11) (coe v4) (coe v12))
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                MAlonzo.Code.Once.Type.C_TVar_104 v6
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_PEff_90 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PEff_90 v5 v6
                  -> let v7 = d_matchesPolyType_570 (coe v3) (coe v5) in
                     coe
                       (let v8 = d_matchesPolyType_570 (coe v4) (coe v6) in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe MAlonzo.Code.Once.Type.C_PEff_90 (coe v9) (coe v10))
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                MAlonzo.Code.Once.Type.C_TVar_104 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v3
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v4
                  -> let v5 = coe d__'8799'PF__294 v3 v4 in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                            -> if coe v6
                                 then coe
                                        seq (coe v7)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0))
                                 else coe
                                        seq (coe v7)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_104 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Pν'45'type_94 v3
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Pν'45'type_94 v4
                  -> let v5 = coe d__'8799'PF__294 v3 v4 in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                            -> if coe v6
                                 then coe
                                        seq (coe v7)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0))
                                 else coe
                                        seq (coe v7)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_104 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_PInt_96
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PInt_96
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_TVar_104 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_PFloat_98
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PFloat_98
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_TVar_104 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_PStr_100
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PStr_100
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_TVar_104 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_PBuffer_102
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PBuffer_102
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_TVar_104 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_TVar_104 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.substituteTVar
d_substituteTVar_748 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70
d_substituteTVar_748 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_PUnit_80 -> coe v2
      MAlonzo.Code.Once.Type.C_PVoid_82 -> coe v2
      MAlonzo.Code.Once.Type.C__P'42'__84 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__P'42'__84
             (coe d_substituteTVar_748 (coe v0) (coe v1) (coe v3))
             (coe d_substituteTVar_748 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Type.C__P'43'__86 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__P'43'__86
             (coe d_substituteTVar_748 (coe v0) (coe v1) (coe v3))
             (coe d_substituteTVar_748 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88
             (coe d_substituteTVar_748 (coe v0) (coe v1) (coe v3)) (coe v4)
             (coe d_substituteTVar_748 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Type.C_PEff_90 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C_PEff_90
             (coe d_substituteTVar_748 (coe v0) (coe v1) (coe v3))
             (coe d_substituteTVar_748 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Pν'45'type_94 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_PInt_96 -> coe v2
      MAlonzo.Code.Once.Type.C_PFloat_98 -> coe v2
      MAlonzo.Code.Once.Type.C_PStr_100 -> coe v2
      MAlonzo.Code.Once.Type.C_PBuffer_102 -> coe v2
      MAlonzo.Code.Once.Type.C_TVar_104 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v3)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe v1)
                       else coe seq (coe v6) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.InferElabResult
d_InferElabResult_814 a0 a1 = ()
data T_InferElabResult_814
  = C_success_828 MAlonzo.Code.Once.Type.T_Type_34
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 Integer Integer
                  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 |
    C_failure_830 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_838 a0 a1 a2 = ()
data T_CheckElabResult_838
  = C_success_852 MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 Integer
                  Integer MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 |
    C_failure_854 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.PolyUsage
d_PolyUsage_856 :: Integer -> ()
d_PolyUsage_856 = erased
-- Once.TypeCheck.Elaborate.PolyInferResult
d_PolyInferResult_862 a0 a1 = ()
data T_PolyInferResult_862
  = C_success_876 MAlonzo.Code.Once.Type.T_PolyType_70
                  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 Integer Integer
                  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 |
    C_failure_878 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.PolyCheckResult
d_PolyCheckResult_886 a0 a1 a2 = ()
data T_PolyCheckResult_886
  = C_success_900 MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52
                  Integer Integer MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 |
    C_failure_902 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.Imports
d_Imports_904 :: ()
d_Imports_904 = erased
-- Once.TypeCheck.Elaborate.emptyImports
d_emptyImports_906 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyImports_906
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Elaborate.NamedCtx
d_NamedCtx_908 = ()
data T_NamedCtx_908
  = C_mkCtx_930 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 Integer
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Elaborate.NamedCtx.size
d_size_920 :: T_NamedCtx_908 -> Integer
d_size_920 v0
  = case coe v0 of
      C_mkCtx_930 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.named
d_named_922 ::
  T_NamedCtx_908 -> [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_922 v0
  = case coe v0 of
      C_mkCtx_930 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.debruijn
d_debruijn_924 ::
  T_NamedCtx_908 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_924 v0
  = case coe v0 of
      C_mkCtx_930 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.freshCounter
d_freshCounter_926 :: T_NamedCtx_908 -> Integer
d_freshCounter_926 v0
  = case coe v0 of
      C_mkCtx_930 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.imports
d_imports_928 ::
  T_NamedCtx_908 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_928 v0
  = case coe v0 of
      C_mkCtx_930 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.emptyCtx
d_emptyCtx_932 :: T_NamedCtx_908
d_emptyCtx_932
  = coe
      C_mkCtx_930 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe d_emptyImports_906)
-- Once.TypeCheck.Elaborate.ctxWithImports
d_ctxWithImports_934 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_908
d_ctxWithImports_934 v0
  = coe
      C_mkCtx_930 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0)
-- Once.TypeCheck.Elaborate.ctxWithImportsAndSelf
d_ctxWithImportsAndSelf_938 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_NamedCtx_908
d_ctxWithImportsAndSelf_938 v0 v1 v2
  = coe
      d_ctxWithImports_934
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
         (coe v0))
-- Once.TypeCheck.Elaborate.extendNamedCtx
d_extendNamedCtx_946 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_NamedCtx_908
d_extendNamedCtx_946 v0 v1 v2
  = case coe v0 of
      C_mkCtx_930 v3 v4 v5 v6 v7
        -> coe
             C_mkCtx_930 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v5) (coe v2))
             (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.bumpFresh
d_bumpFresh_962 :: T_NamedCtx_908 -> T_NamedCtx_908
d_bumpFresh_962 v0
  = case coe v0 of
      C_mkCtx_930 v1 v2 v3 v4 v5
        -> coe
             C_mkCtx_930 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.freshTVar
d_freshTVar_974 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_974 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Elaborate.PolyImports
d_PolyImports_978 :: ()
d_PolyImports_978 = erased
-- Once.TypeCheck.Elaborate.embedImports
d_embedImports_980 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_embedImports_980 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe MAlonzo.Code.Once.Type.d_embed_108 (coe v4)))
                    (coe d_embedImports_980 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.PolyNamedCtx
d_PolyNamedCtx_988 = ()
data T_PolyNamedCtx_988
  = C_mkPolyCtx_1010 Integer
                     [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                     MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 Integer
                     [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Elaborate.PolyNamedCtx.size
d_size_1000 :: T_PolyNamedCtx_988 -> Integer
d_size_1000 v0
  = case coe v0 of
      C_mkPolyCtx_1010 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.PolyNamedCtx.named
d_named_1002 ::
  T_PolyNamedCtx_988 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_1002 v0
  = case coe v0 of
      C_mkPolyCtx_1010 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.PolyNamedCtx.polyCtx
d_polyCtx_1004 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6
d_polyCtx_1004 v0
  = case coe v0 of
      C_mkPolyCtx_1010 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.PolyNamedCtx.freshCounter
d_freshCounter_1006 :: T_PolyNamedCtx_988 -> Integer
d_freshCounter_1006 v0
  = case coe v0 of
      C_mkPolyCtx_1010 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.PolyNamedCtx.polyImports
d_polyImports_1008 ::
  T_PolyNamedCtx_988 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polyImports_1008 v0
  = case coe v0 of
      C_mkPolyCtx_1010 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.emptyPolyCtx
d_emptyPolyCtx_1012 :: T_PolyNamedCtx_988
d_emptyPolyCtx_1012
  = coe
      C_mkPolyCtx_1010 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.PolySyntax.C_P'8709'_8)
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate.polyCtxWithImports
d_polyCtxWithImports_1014 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_PolyNamedCtx_988
d_polyCtxWithImports_1014 v0
  = coe
      C_mkPolyCtx_1010 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.PolySyntax.C_P'8709'_8)
      (coe (0 :: Integer)) (coe d_embedImports_980 (coe v0))
-- Once.TypeCheck.Elaborate.polyCtxWithImportsAndSelf
d_polyCtxWithImportsAndSelf_1018 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_PolyNamedCtx_988
d_polyCtxWithImportsAndSelf_1018 v0 v1 v2
  = coe
      d_polyCtxWithImports_1014
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
         (coe v0))
-- Once.TypeCheck.Elaborate.extendPolyNamedCtx
d_extendPolyNamedCtx_1026 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_PolyNamedCtx_988
d_extendPolyNamedCtx_1026 v0 v1 v2
  = case coe v0 of
      C_mkPolyCtx_1010 v3 v4 v5 v6 v7
        -> coe
             C_mkPolyCtx_1010 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.PolySyntax.du__P'44'__16 (coe v5)
                (coe MAlonzo.Code.Once.Type.d_embed_108 (coe v2)))
             (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.bumpPolyFresh
d_bumpPolyFresh_1042 :: T_PolyNamedCtx_988 -> T_PolyNamedCtx_988
d_bumpPolyFresh_1042 v0
  = case coe v0 of
      C_mkPolyCtx_1010 v1 v2 v3 v4 v5
        -> coe
             C_mkPolyCtx_1010 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.setPolyFresh
d_setPolyFresh_1054 ::
  T_PolyNamedCtx_988 -> Integer -> T_PolyNamedCtx_988
d_setPolyFresh_1054 v0 v1
  = case coe v0 of
      C_mkPolyCtx_1010 v2 v3 v4 v5 v6
        -> coe
             C_mkPolyCtx_1010 (coe v2) (coe v3) (coe v4) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.extendPolyNamedCtxPoly
d_extendPolyNamedCtxPoly_1066 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 -> T_PolyNamedCtx_988
d_extendPolyNamedCtxPoly_1066 v0 v1 v2
  = case coe v0 of
      C_mkPolyCtx_1010 v3 v4 v5 v6 v7
        -> coe
             C_mkPolyCtx_1010 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe MAlonzo.Code.Once.Type.C_Unit_44))
             (coe
                MAlonzo.Code.Once.Surface.PolySyntax.du__P'44'__16 (coe v5)
                (coe v2))
             (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.extendPolyNamedCtxPolyQ
d_extendPolyNamedCtxPolyQ_1082 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> T_PolyNamedCtx_988
d_extendPolyNamedCtxPolyQ_1082 v0 v1 v2 v3
  = case coe v0 of
      C_mkPolyCtx_1010 v4 v5 v6 v7 v8
        -> coe
             C_mkPolyCtx_1010 (coe addInt (coe (1 :: Integer)) (coe v4))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v5)
                (coe v1) (coe MAlonzo.Code.Once.Type.C_Unit_44))
             (coe
                MAlonzo.Code.Once.Surface.PolySyntax.C__P'44'_'94'__12 v6 v2 v3)
             (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.findVarIndex
d_findVarIndex_1102 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_findVarIndex_1102 v0 v1
  = case coe v0 of
      C_mkCtx_930 v2 v3 v4 v5 v6
        -> coe du_go_1124 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_1124 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_go_1124 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 = du_go_1124 v5 v7 v8
du_go_1124 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_go_1124 v0 v1 v2
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
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                              else coe
                                     seq (coe v11)
                                     (let v12 = coe du_go_1124 (coe v0) (coe v4) (coe v6) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                  (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v13)
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.Subst
d_Subst_1196 :: ()
d_Subst_1196 = erased
-- Once.TypeCheck.Elaborate.emptySubst
d_emptySubst_1198 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptySubst_1198
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Elaborate.extendSubst
d_extendSubst_1200 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_1200 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.TypeCheck.Elaborate.lookupSubst
d_lookupSubst_1208 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_70
d_lookupSubst_1208 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupSubst_1208 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.applySubstPF
d_applySubstPF_1238 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_68 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_68
d_applySubstPF_1238 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_PK_72 v2
        -> coe
             MAlonzo.Code.Once.Type.C_PK_72
             (coe d_applySubst_1240 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_PId_74 -> coe v1
      MAlonzo.Code.Once.Type.C__P'8853'__76 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__P'8853'__76
             (coe d_applySubstPF_1238 (coe v0) (coe v2))
             (coe d_applySubstPF_1238 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__P'8855'__78 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__P'8855'__78
             (coe d_applySubstPF_1238 (coe v0) (coe v2))
             (coe d_applySubstPF_1238 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.applySubst
d_applySubst_1240 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70
d_applySubst_1240 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_PUnit_80 -> coe v1
      MAlonzo.Code.Once.Type.C_PVoid_82 -> coe v1
      MAlonzo.Code.Once.Type.C__P'42'__84 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__P'42'__84
             (coe d_applySubst_1240 (coe v0) (coe v2))
             (coe d_applySubst_1240 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__P'43'__86 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__P'43'__86
             (coe d_applySubst_1240 (coe v0) (coe v2))
             (coe d_applySubst_1240 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88
             (coe d_applySubst_1240 (coe v0) (coe v2)) (coe v3)
             (coe d_applySubst_1240 (coe v0) (coe v4))
      MAlonzo.Code.Once.Type.C_PEff_90 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C_PEff_90
             (coe d_applySubst_1240 (coe v0) (coe v2))
             (coe d_applySubst_1240 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v2
        -> coe
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92
             (coe d_applySubstPF_1238 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Pν'45'type_94 v2
        -> coe
             MAlonzo.Code.Once.Type.C_Pν'45'type_94
             (coe d_applySubstPF_1238 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_PInt_96 -> coe v1
      MAlonzo.Code.Once.Type.C_PFloat_98 -> coe v1
      MAlonzo.Code.Once.Type.C_PStr_100 -> coe v1
      MAlonzo.Code.Once.Type.C_PBuffer_102 -> coe v1
      MAlonzo.Code.Once.Type.C_TVar_104 v2
        -> let v3 = d_lookupSubst_1208 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v4
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.matchWithSubst
d_matchWithSubst_1322 ::
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_matchWithSubst_1322 v0 v1 v2
  = let v3
          = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
            coe
              (case coe v1 of
                 MAlonzo.Code.Once.Type.C_TVar_104 v4
                   -> coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                           (coe d_extendSubst_1200 (coe v2) (coe v4) (coe v0)))
                 _ -> coe v3) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_PUnit_80
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PUnit_80
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                MAlonzo.Code.Once.Type.C_TVar_104 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v4) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C_PVoid_82
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PVoid_82
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                MAlonzo.Code.Once.Type.C_TVar_104 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v4) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C__P'42'__84 v4 v5
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__P'42'__84 v6 v7
                  -> let v8 = d_matchWithSubst_1322 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> let v12 = d_matchWithSubst_1322 (coe v5) (coe v7) (coe v11) in
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
                                                               MAlonzo.Code.Once.Type.C__P'42'__84
                                                               (coe v10) (coe v14))
                                                            (coe v15))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_104 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v6) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C__P'43'__86 v4 v5
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__P'43'__86 v6 v7
                  -> let v8 = d_matchWithSubst_1322 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> let v12 = d_matchWithSubst_1322 (coe v5) (coe v7) (coe v11) in
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
                                                               MAlonzo.Code.Once.Type.C__P'43'__86
                                                               (coe v10) (coe v14))
                                                            (coe v15))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_104 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v6) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v4 v5 v6
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v7 v8 v9
                  -> let v10 = d_matchWithSubst_1322 (coe v4) (coe v7) (coe v2) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> let v14 = d_matchWithSubst_1322 (coe v6) (coe v9) (coe v13) in
                                      coe
                                        (case coe v14 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                             -> case coe v15 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88
                                                               (coe v12) (coe v5) (coe v16))
                                                            (coe v17))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v14
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_104 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v7) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C_PEff_90 v4 v5
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PEff_90 v6 v7
                  -> let v8 = d_matchWithSubst_1322 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> let v12 = d_matchWithSubst_1322 (coe v5) (coe v7) (coe v11) in
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
                                                               MAlonzo.Code.Once.Type.C_PEff_90
                                                               (coe v10) (coe v14))
                                                            (coe v15))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_104 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v6) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v5
                  -> let v6 = coe d__'8799'PF__294 v4 v5 in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                                              (coe v2)))
                                 else coe
                                        seq (coe v8)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_104 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v5) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C_Pν'45'type_94 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Pν'45'type_94 v5
                  -> let v6 = coe d__'8799'PF__294 v4 v5 in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                                              (coe v2)))
                                 else coe
                                        seq (coe v8)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_104 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v5) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C_PInt_96
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PInt_96
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                MAlonzo.Code.Once.Type.C_TVar_104 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v4) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C_PFloat_98
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PFloat_98
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                MAlonzo.Code.Once.Type.C_TVar_104 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v4) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C_PStr_100
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PStr_100
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                MAlonzo.Code.Once.Type.C_TVar_104 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v4) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C_PBuffer_102
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_PBuffer_102
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                MAlonzo.Code.Once.Type.C_TVar_104 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe d_extendSubst_1200 (coe v2) (coe v4) (coe v0)))
                _ -> coe v3
         MAlonzo.Code.Once.Type.C_TVar_104 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe d_extendSubst_1200 (coe v2) (coe v4) (coe v1)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.instantiate
d_instantiate_1708 ::
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instantiate_1708 v0 v1
  = coe du_go_1718 (coe v0) (coe v1) (coe d_emptySubst_1198)
-- Once.TypeCheck.Elaborate._.go
d_go_1718 ::
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1718 ~v0 ~v1 v2 v3 v4 = du_go_1718 v2 v3 v4
du_go_1718 ::
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1718 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PUnit_80
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_PVoid_82
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C__P'42'__84 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__P'42'__84
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_1718 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_1718 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C__P'43'__86 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__P'43'__86
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_1718 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_1718 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_1718 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_1718 (coe v5)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C_PEff_90 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C_PEff_90
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_1718 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_1718 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_1718 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Pν'45'type_94 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_PInt_96
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_PFloat_98
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_PStr_100
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_PBuffer_102
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_TVar_104 v3
        -> let v4 = d_lookupSubst_1208 (coe v2) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v1)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._P⇒_
d__P'8658'__1850 ::
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70
d__P'8658'__1850 v0 v1
  = coe
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 (coe v0)
      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)
-- Once.TypeCheck.Elaborate.builtinPolyType
d_builtinPolyType_1858 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_builtinPolyType_1858 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         l | (==) l ("apply" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        MAlonzo.Code.Once.Type.C__P'42'__84
                        (coe
                           d__P'8658'__1850
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_104
                        (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_pfst''_114
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_psnd''_124
                              (d__P'8658'__1850
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_104
                                    (coe d_freshTVar_974 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_104
                                    (coe
                                       d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                              (coe
                                 MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("arr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        d__P'8658'__1850
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.C_PEff_90
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_parr''_274
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("case" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        d__P'8658'__1850
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe
                        d__P'8658'__1850
                        (coe
                           d__P'8658'__1850
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe d_freshTVar_974 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                        (coe
                           d__P'8658'__1850
                           (coe
                              MAlonzo.Code.Once.Type.C__P'43'__86
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_104
                                 (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe
                                 d_freshTVar_974 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                              (coe
                                 MAlonzo.Code.Once.Surface.PolySyntax.C_pcase''_156
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_104
                                    (coe d_freshTVar_974 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_104
                                    (coe
                                       d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))
                                 (coe
                                    MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                 (coe
                                    MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_104
                                       (coe d_freshTVar_974 (coe v1)))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe
                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                             (coe
                                                MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_104
                                       (coe
                                          d_freshTVar_974
                                          (coe addInt (coe (1 :: Integer)) (coe v1))))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe
                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                     (coe addInt (coe (3 :: Integer)) (coe v1))))
         l | (==) l ("compose" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        d__P'8658'__1850
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe
                        d__P'8658'__1850
                        (coe
                           d__P'8658'__1850
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe
                           d__P'8658'__1850
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe
                                 d_freshTVar_974 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                              (coe
                                 MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_104
                                    (coe
                                       d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))
                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                 (coe
                                    MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                 (coe
                                    MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_104
                                       (coe d_freshTVar_974 (coe v1)))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                     (coe addInt (coe (3 :: Integer)) (coe v1))))
         l | (==) l ("curry" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        d__P'8658'__1850
                        (coe
                           MAlonzo.Code.Once.Type.C__P'42'__84
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe
                        d__P'8658'__1850
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                        (coe
                           d__P'8658'__1850
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe
                                 d_freshTVar_974 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                              (coe
                                 MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84
                                 (coe
                                    MAlonzo.Code.Once.Type.C__P'42'__84
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_104
                                       (coe d_freshTVar_974 (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_104
                                       (coe
                                          d_freshTVar_974
                                          (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                 (coe
                                    MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                 (coe
                                    MAlonzo.Code.Once.Surface.PolySyntax.C_ppair_104
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                     (coe addInt (coe (3 :: Integer)) (coe v1))))
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        MAlonzo.Code.Once.Type.C__P'42'__84
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_pfst''_114
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("id" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                     (coe addInt (coe (1 :: Integer)) (coe v1))))
         l | (==) l ("initial" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850 (coe MAlonzo.Code.Once.Type.C_PVoid_82)
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_pabsurd_170
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (1 :: Integer)) (coe v1))))
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.Type.C__P'43'__86
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_pinl''_134
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_104
                        (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))
                     (coe
                        MAlonzo.Code.Once.Type.C__P'43'__86
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_pinr''_144
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        d__P'8658'__1850
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        d__P'8658'__1850
                        (coe
                           d__P'8658'__1850
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104
                              (coe d_freshTVar_974 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                        (coe
                           d__P'8658'__1850
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C__P'42'__84
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_104
                                 (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_104
                                 (coe
                                    d_freshTVar_974 (coe addInt (coe (2 :: Integer)) (coe v1))))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                              (coe
                                 MAlonzo.Code.Once.Surface.PolySyntax.C_ppair_104
                                 (coe
                                    MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_104
                                       (coe d_freshTVar_974 (coe v1)))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe
                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_104
                                       (coe d_freshTVar_974 (coe v1)))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                     (coe addInt (coe (3 :: Integer)) (coe v1))))
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        MAlonzo.Code.Once.Type.C__P'42'__84
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_104
                           (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_104
                        (coe d_freshTVar_974 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe
                           MAlonzo.Code.Once.Surface.PolySyntax.C_psnd''_124
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("terminal" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     d__P'8658'__1850
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_104 (coe d_freshTVar_974 (coe v1)))
                     (coe MAlonzo.Code.Once.Type.C_PUnit_80))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72
                        (coe MAlonzo.Code.Once.Surface.PolySyntax.C_punit_162))
                     (coe addInt (coe (1 :: Integer)) (coe v1))))
         l | (==) l ("unit" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Type.C_PUnit_80)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe MAlonzo.Code.Once.Surface.PolySyntax.C_punit_162) (coe v1)))
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.builtinType
d_builtinType_1944 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_builtinType_1944 v0 v1
  = let v2 = d_builtinPolyType_1858 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8 = MAlonzo.Code.Once.Type.d_extract_144 (coe v4) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> let v10
                                            = coe
                                                MAlonzo.Code.Once.Surface.PolySyntax.d_unsafeCoerceExpr_324
                                                (0 :: Integer)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.PolySyntax.C_P'8709'_8)
                                                (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) v4
                                                v9 v6 in
                                      coe
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v10) (coe v7))))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.lookupImport
d_lookupImport_2024 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_34
d_lookupImport_2024 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupImport_2024 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.lookupVar
d_lookupVar_2058 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupVar_2058 v0 v1
  = case coe v0 of
      C_mkCtx_930 v2 v3 v4 v5 v6
        -> coe
             du_go_2082 (coe v6) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_2082 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2082 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_go_2082 v4 v5 v6 v7 v8 v9
du_go_2082 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2082 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      []
        -> case coe v4 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> let v6 = d_builtinPolyType_1858 (coe v1) (coe v5) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> case coe v9 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                       -> let v12 = MAlonzo.Code.Once.Type.d_extract_144 (coe v8) in
                                          coe
                                            (case coe v12 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                 -> let v14
                                                          = coe
                                                              MAlonzo.Code.Once.Surface.PolySyntax.d_unsafeCoerceExpr_324
                                                              (0 :: Integer)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.PolySyntax.C_P'8709'_8)
                                                              v4 v8 v13 v10 in
                                                    coe
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  d_weakenFromEmpty_12
                                                                  (coe (0 :: Integer)) (coe v4)
                                                                  (coe v13) (coe v14))
                                                               (coe v11))))
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> case coe v12 of
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                               -> case coe v15 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe v14)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    d_weakenFromEmpty_12
                                                                                    (coe
                                                                                       (0 ::
                                                                                          Integer))
                                                                                    (coe v4)
                                                                                    (coe v14)
                                                                                    (coe v16))
                                                                                 (coe v17)))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> let v13
                                                                 = d_lookupImport_2024
                                                                     (coe v0) (coe v1) in
                                                           coe
                                                             (case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v14)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.Surface.Syntax.C_prim_392
                                                                                v1)
                                                                             (coe v5)))
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe v13
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v9 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            d_weakenFromEmpty_12
                                                            (coe (0 :: Integer)) (coe v4) (coe v8)
                                                            (coe v10))
                                                         (coe v11)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v7 = d_lookupImport_2024 (coe v0) (coe v1) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_prim_392
                                                        v1)
                                                     (coe v5)))
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v7 v8 v9
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v6 v7
        -> case coe v4 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v9 v10 v11
               -> let v12 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    (let v13
                           = let v13
                                   = coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                       erased
                                       (\ v13 ->
                                          coe
                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                            (coe v1))
                                       (coe
                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                          (coe v1)
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Context.d_name_14
                                             (coe v6))) in
                             coe
                               (case coe v13 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                    -> if coe v14
                                         then coe
                                                seq (coe v15)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                                         (coe v5))))
                                         else coe
                                                seq (coe v15)
                                                (let v16
                                                       = coe
                                                           du_go_2082 (coe v0) (coe v1) (coe v12)
                                                           (coe v7) (coe v9) (coe v5) in
                                                 coe
                                                   (case coe v16 of
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                        -> case coe v17 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                               -> case coe v19 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe v18)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Postulates.d_coerceQuantity_30
                                                                                    v12 v9 v10 v18
                                                                                    v11 v11
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Thinning.du_weaken_476
                                                                                       v9 v10 v18
                                                                                       v11 v20))
                                                                                 (coe v21)))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> coe v16
                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Once.Type.C_Many_10
                            -> let v14
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v14 ->
                                            coe
                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                              (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                            (coe v1)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Context.d_name_14
                                               (coe v6))) in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                      -> if coe v15
                                           then coe
                                                  seq (coe v16)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                              (coe
                                                                 MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                                           (coe v5))))
                                           else coe
                                                  seq (coe v16)
                                                  (let v17
                                                         = coe
                                                             du_go_2082 (coe v0) (coe v1) (coe v12)
                                                             (coe v7) (coe v9) (coe v5) in
                                                   coe
                                                     (case coe v17 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                          -> case coe v18 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                 -> case coe v20 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                        -> coe
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v19)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Thinning.du_weaken_476
                                                                                      v9 v10 v19 v11
                                                                                      v21)
                                                                                   (coe v22)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> coe v17
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.lookupPolyImport
d_lookupPolyImport_2268 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_70
d_lookupPolyImport_2268 v0 v1
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
                              else coe
                                     seq (coe v8) (coe d_lookupPolyImport_2268 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.lookupPolyVar
d_lookupPolyVar_2302 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPolyVar_2302 v0 v1
  = case coe v0 of
      C_mkPolyCtx_1010 v2 v3 v4 v5 v6
        -> coe
             du_go_2326 (coe v6) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_2326 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2326 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_go_2326 v4 v5 v6 v7 v8 v9
du_go_2326 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2326 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      []
        -> case coe v4 of
             MAlonzo.Code.Once.Surface.PolySyntax.C_P'8709'_8
               -> let v6 = d_builtinPolyType_1858 (coe v1) (coe v5) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> case coe v9 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.PolySyntax.d_pweakenFromEmpty_362
                                                     (coe (0 :: Integer)) (coe v4) (coe v8)
                                                     (coe v10))
                                                  (coe v11)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> let v7 = d_lookupPolyImport_2268 (coe v0) (coe v1) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Once.Surface.PolySyntax.C_pprim_282
                                                 v1)
                                              (coe v5)))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Surface.PolySyntax.C__P'44'_'94'__12 v7 v8 v9
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v6 v7
        -> case coe v4 of
             MAlonzo.Code.Once.Surface.PolySyntax.C_P'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.PolySyntax.C__P'44'_'94'__12 v9 v10 v11
               -> let v12 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    (let v13
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v1))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_14 (coe v6))) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then coe
                                        seq (coe v15)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.PolySyntax.C_pvar_60
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                                 (coe v5))))
                                 else coe
                                        seq (coe v15)
                                        (let v16
                                               = coe
                                                   du_go_2326 (coe v0) (coe v1) (coe v12) (coe v7)
                                                   (coe v9) (coe v5) in
                                         coe
                                           (case coe v16 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                -> case coe v17 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                       -> case coe v19 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v18)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.PolySyntax.d_pweaken_354
                                                                            v12 v9 v18 v10 v11 v20)
                                                                         (coe v21)))
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe v16
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.findPolyVarIndex
d_findPolyVarIndex_2440 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_findPolyVarIndex_2440 v0 v1
  = case coe v0 of
      C_mkPolyCtx_1010 v2 v3 v4 v5 v6
        -> coe du_go_2462 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_2462 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_go_2462 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 = du_go_2462 v5 v7 v8
du_go_2462 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_go_2462 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Surface.PolySyntax.C_P'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.PolySyntax.C__P'44'_'94'__12 v6 v7 v8
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
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                              else coe
                                     seq (coe v11)
                                     (let v12 = coe du_go_2462 (coe v0) (coe v4) (coe v6) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                  (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v13)
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabImpl
d_checkElabImpl_2538 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_CheckElabResult_838
d_checkElabImpl_2538 v0 v1 v2
  = let v3
          = let v3 = d_inferElabImpl_2542 (coe v0) (coe v1) in
            coe
              (case coe v3 of
                 C_success_828 v4 v5 v6 v7 v8
                   -> let v9 = d__'8799'T__40 (coe v4) (coe v2) in
                      coe
                        (case coe v9 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                             -> if coe v10
                                  then coe
                                         seq (coe v11)
                                         (coe C_success_852 (coe v5) (coe v6) (coe v7) (coe v8))
                                  else coe
                                         seq (coe v11)
                                         (coe
                                            C_failure_854
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               ("Type mismatch: expected " :: Data.Text.Text)
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  (MAlonzo.Code.Once.Type.d_showType_368 (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                     (" but got " :: Data.Text.Text)
                                                     (MAlonzo.Code.Once.Type.d_showType_368
                                                        (coe v4))))))
                           _ -> MAlonzo.RTE.mazUnreachableError)
                 C_failure_830 v4 -> coe C_failure_854 (coe v4)
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v4 v5
           -> let v6
                    = coe
                        C_failure_854
                        (coe ("Lambda requires function type" :: Data.Text.Text)) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v7 v8 v9
                     -> let v10
                              = d_checkElabImpl_2538
                                  (coe d_extendNamedCtx_946 (coe v0) (coe v4) (coe v7)) (coe v5)
                                  (coe v9) in
                        coe
                          (case coe v10 of
                             C_success_852 v11 v12 v13 v14
                               -> coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Once.Type.d__'8804'q__28
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140
                                          (coe v14) (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                       (coe v8))
                                    (coe
                                       C_success_852
                                       (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_182 v11)
                                       (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154
                                          (coe v14)))
                                    (coe
                                       C_failure_854
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("Parameter '" :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v4
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("' used with quantity " :: Data.Text.Text)
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   (MAlonzo.Code.Once.Type.d_showQuantity_30
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140
                                                         (coe v14)
                                                         (coe
                                                            MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      (" but declared with quantity "
                                                       ::
                                                       Data.Text.Text)
                                                      (MAlonzo.Code.Once.Type.d_showQuantity_30
                                                         (coe v8))))))))
                             C_failure_854 v11 -> coe v10
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v6)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.inferElabImpl
d_inferElabImpl_2542 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814
d_inferElabImpl_2542 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> let v3
                 = coe
                     du_go_2082 (coe d_imports_928 (coe v0)) (coe v2)
                     (coe d_size_920 (coe v0)) (coe d_named_922 (coe v0))
                     (coe d_debruijn_924 (coe v0)) (coe d_freshCounter_926 (coe v0)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> let v9
                                         = coe
                                             du_go_1124 (coe v2) (coe d_named_922 (coe v0))
                                             (coe d_debruijn_924 (coe v0)) in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                          -> coe
                                               C_success_828 (coe v5) (coe v7) (coe (0 :: Integer))
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.d_singleUse_66
                                                  (coe d_size_920 (coe v0)) (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.du_lookupQuantity_38
                                                     (coe d_debruijn_924 (coe v0)) (coe v10)))
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> coe
                                               C_success_828 (coe v5) (coe v7) (coe (0 :: Integer))
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                  (coe d_size_920 (coe v0)))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_830
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Unbound variable: " :: Data.Text.Text) v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> let v4
                 = coe
                     du_go_2082 (coe d_imports_928 (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("." :: Data.Text.Text) v2))
                     (coe d_size_920 (coe v0)) (coe d_named_922 (coe v0))
                     (coe d_debruijn_924 (coe v0)) (coe d_freshCounter_926 (coe v0)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> coe
                                     C_success_828 (coe v6) (coe v8) (coe (0 :: Integer)) (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                        (coe d_size_920 (coe v0)))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_830
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Unbound qualified variable: " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("@" :: Data.Text.Text) v3)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v2 v3
        -> coe
             du_inferApp_2764 (coe v0) (coe v3)
             (coe d_inferElabImpl_2542 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v2 v3
        -> coe
             C_failure_830
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Lambda without type annotation not supported in inference mode.\n"
                 ::
                 Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Add a type annotation or use a type-annotated expression.\n"
                    ::
                    Data.Text.Text)
                   ("Example: (\\x -> body) : A -> B" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v2 v3 v4
        -> let v5 = d_inferElabImpl_2542 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_828 v6 v7 v8 v9 v10
                  -> let v11
                           = d_inferElabImpl_2542
                               (coe du_extendNamedCtx''_3046 (coe v0) (coe v2) (coe v6) (coe v9))
                               (coe v4) in
                     coe
                       (case coe v11 of
                          C_success_828 v12 v13 v14 v15 v16
                            -> coe
                                 C_success_828 (coe v12)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_let''_290 v6 v7 v13)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8)
                                    (coe addInt (coe (1 :: Integer)) (coe v14)))
                                 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154 (coe v16)))
                          C_failure_830 v12 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_830 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v2 v3
        -> let v4 = d_inferElabImpl_2542 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_828 v5 v6 v7 v8 v9
                  -> let v10
                           = d_inferElabImpl_2542
                               (coe du_bumpFresh''_2940 (coe v0) (coe v8)) (coe v3) in
                     coe
                       (case coe v10 of
                          C_success_828 v11 v12 v13 v14 v15
                            -> coe
                                 C_success_828
                                 (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v5) (coe v11))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_214 v6 v12)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v13))
                                 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v9)
                                    (coe v15))
                          C_failure_830 v11 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_830 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v2 v3 v4 v5 v6
        -> coe
             du_inferCase_3146 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe d_inferElabImpl_2542 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe
             C_success_828 (coe MAlonzo.Code.Once.Type.C_Unit_44)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_272)
             (coe (0 :: Integer)) (coe d_freshCounter_926 (coe v0))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_920 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v2
        -> coe
             C_success_828 (coe MAlonzo.Code.Once.Type.C_Int_60)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_int_296 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_926 (coe v0))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_920 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v2
        -> coe
             C_success_828 (coe MAlonzo.Code.Once.Type.C_Str_64)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_str_302 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_926 (coe v0))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_920 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v2 v3
        -> coe d_inferElabImpl_2542 (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v2 v3 v4
        -> coe
             du_inferOp_3258 (coe v0) (coe v2) (coe v4)
             (coe d_inferElabImpl_2542 (coe v0) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v3
        -> coe
             du_inferNeg_3306 (coe d_inferElabImpl_2542 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferApp
d_inferApp_2764 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_inferApp_2764 v0 ~v1 v2 v3 = du_inferApp_2764 v0 v2 v3
du_inferApp_2764 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814 -> T_InferElabResult_814
du_inferApp_2764 v0 v1 v2
  = case coe v2 of
      C_success_828 v3 v4 v5 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__48 v8 v9
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__50 v8 v9
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v8 v9 v10
               -> coe
                    du_inferArg_2798 (coe v8) (coe v9) (coe v10) (coe v4) (coe v5)
                    (coe v7)
                    (coe
                       d_inferElabImpl_2542 (coe du_bumpFreshTo_2786 (coe v0) (coe v6))
                       (coe v1))
             MAlonzo.Code.Once.Type.C_Eff_54 v8 v9
               -> coe
                    du_inferArgEff_2864 (coe v8) (coe v9) (coe v4) (coe v5) (coe v7)
                    (coe
                       d_inferElabImpl_2542 (coe du_bumpFreshToEff_2852 (coe v0) (coe v6))
                       (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v8
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v8
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    C_failure_830
                    (coe ("Expected function type in application" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_830 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.bumpFreshTo
d_bumpFreshTo_2786 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_NamedCtx_908 -> Integer -> T_NamedCtx_908
d_bumpFreshTo_2786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_bumpFreshTo_2786 v10 v11
du_bumpFreshTo_2786 :: T_NamedCtx_908 -> Integer -> T_NamedCtx_908
du_bumpFreshTo_2786 v0 v1
  = case coe v0 of
      C_mkCtx_930 v2 v3 v4 v5 v6
        -> coe C_mkCtx_930 (coe v2) (coe v3) (coe v4) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferArg
d_inferArg_2798 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_inferArg_2798 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 v9 v10
  = du_inferArg_2798 v3 v4 v5 v6 v7 v9 v10
du_inferArg_2798 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
du_inferArg_2798 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_success_828 v7 v8 v9 v10 v11
        -> let v12 = d__'8799'T__40 (coe v0) (coe v7) in
           coe
             (case coe v12 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                  -> if coe v13
                       then coe
                              seq (coe v14)
                              (coe
                                 C_success_828 (coe v2)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_app_194 v7 v1 v3 v8)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v4) (coe v9))
                                 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v5)
                                    (coe v11)))
                       else coe
                              seq (coe v14)
                              (coe
                                 C_failure_830
                                 (coe ("Type mismatch in application" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_830 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.bumpFreshToEff
d_bumpFreshToEff_2852 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_NamedCtx_908 -> Integer -> T_NamedCtx_908
d_bumpFreshToEff_2852 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_bumpFreshToEff_2852 v9 v10
du_bumpFreshToEff_2852 ::
  T_NamedCtx_908 -> Integer -> T_NamedCtx_908
du_bumpFreshToEff_2852 v0 v1
  = case coe v0 of
      C_mkCtx_930 v2 v3 v4 v5 v6
        -> coe C_mkCtx_930 (coe v2) (coe v3) (coe v4) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferArgEff
d_inferArgEff_2864 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_inferArgEff_2864 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_inferArgEff_2864 v3 v4 v5 v6 v8 v9
du_inferArgEff_2864 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
du_inferArgEff_2864 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_828 v6 v7 v8 v9 v10
        -> let v11 = d__'8799'T__40 (coe v0) (coe v6) in
           coe
             (case coe v11 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                  -> if coe v12
                       then coe
                              seq (coe v13)
                              (coe
                                 C_success_828 (coe v1)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_effApp_204 v6 v2 v7)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v8))
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v4)
                                    (coe v10)))
                       else coe
                              seq (coe v13)
                              (coe
                                 C_failure_830
                                 (coe ("Type mismatch in effect application" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_830 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.bumpFresh'
d_bumpFresh''_2940 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_908 -> Integer -> T_NamedCtx_908
d_bumpFresh''_2940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_bumpFresh''_2940 v8 v9
du_bumpFresh''_2940 :: T_NamedCtx_908 -> Integer -> T_NamedCtx_908
du_bumpFresh''_2940 v0 v1
  = case coe v0 of
      C_mkCtx_930 v2 v3 v4 v5 v6
        -> coe C_mkCtx_930 (coe v2) (coe v3) (coe v4) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.extendNamedCtx'
d_extendNamedCtx''_3046 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_908 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> Integer -> T_NamedCtx_908
d_extendNamedCtx''_3046 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
                        v11 v12
  = du_extendNamedCtx''_3046 v9 v10 v11 v12
du_extendNamedCtx''_3046 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> Integer -> T_NamedCtx_908
du_extendNamedCtx''_3046 v0 v1 v2 v3
  = case coe v0 of
      C_mkCtx_930 v4 v5 v6 v7 v8
        -> coe
             C_mkCtx_930 (coe addInt (coe (1 :: Integer)) (coe v4))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v5)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v6) (coe v2))
             (coe v3) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.extendCtx'
d_extendCtx''_3130 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_908 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> Integer -> T_NamedCtx_908
d_extendCtx''_3130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_extendCtx''_3130 v6 v7 v8 v9
du_extendCtx''_3130 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> Integer -> T_NamedCtx_908
du_extendCtx''_3130 v0 v1 v2 v3
  = case coe v0 of
      C_mkCtx_930 v4 v5 v6 v7 v8
        -> coe
             C_mkCtx_930 (coe addInt (coe (1 :: Integer)) (coe v4))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v5)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v6) (coe v2))
             (coe v3) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferCase
d_inferCase_3146 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_inferCase_3146 v0 ~v1 v2 v3 v4 v5 v6
  = du_inferCase_3146 v0 v2 v3 v4 v5 v6
du_inferCase_3146 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814 -> T_InferElabResult_814
du_inferCase_3146 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_828 v6 v7 v8 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__48 v11 v12
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__50 v11 v12
               -> coe
                    du_inferLeft_3166 (coe v0) (coe v3) (coe v4) (coe v11) (coe v12)
                    (coe v7) (coe v8) (coe v10)
                    (coe
                       d_inferElabImpl_2542
                       (coe du_extendCtx''_3130 (coe v0) (coe v1) (coe v11) (coe v9))
                       (coe v2))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v11 v12 v13
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Eff_54 v11 v12
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v11
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v11
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    C_failure_830 (coe ("Expected sum type in case" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_830 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferLeft
d_inferLeft_3166 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_inferLeft_3166 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 ~v10 v11 v12
  = du_inferLeft_3166 v0 v4 v5 v6 v7 v8 v9 v11 v12
du_inferLeft_3166 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
du_inferLeft_3166 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_success_828 v9 v10 v11 v12 v13
        -> coe
             du_inferRight_3184 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
             (coe v9) (coe v10) (coe v11) (coe v13)
             (coe
                d_inferElabImpl_2542
                (coe du_extendCtx''_3130 (coe v0) (coe v1) (coe v4) (coe v12))
                (coe v2))
      C_failure_830 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._._.inferRight
d_inferRight_3184 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_inferRight_3184 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12
                  v13 v14 ~v15 v16 v17
  = du_inferRight_3184 v6 v7 v8 v9 v11 v12 v13 v14 v16 v17
du_inferRight_3184 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
du_inferRight_3184 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_success_828 v10 v11 v12 v13 v14
        -> let v15 = d__'8799'T__40 (coe v5) (coe v10) in
           coe
             (case coe v15 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                  -> if coe v16
                       then coe
                              seq (coe v17)
                              (coe
                                 C_success_828 (coe v10)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_case''_266 v0 v1 v2 v6 v11)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                                       (coe addInt (coe (1 :: Integer)) (coe v7)))
                                    (coe addInt (coe (1 :: Integer)) (coe v12)))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154
                                          (coe v8)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154
                                       (coe v14))))
                       else coe
                              seq (coe v17)
                              (coe
                                 C_failure_830
                                 (coe ("Case branches have different types" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_830 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.bumpFresh'
d_bumpFresh''_3246 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_908 -> Integer -> T_NamedCtx_908
d_bumpFresh''_3246 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_bumpFresh''_3246 v4 v5
du_bumpFresh''_3246 :: T_NamedCtx_908 -> Integer -> T_NamedCtx_908
du_bumpFresh''_3246 v0 v1
  = case coe v0 of
      C_mkCtx_930 v2 v3 v4 v5 v6
        -> coe C_mkCtx_930 (coe v2) (coe v3) (coe v4) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferOp
d_inferOp_3258 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_inferOp_3258 v0 v1 ~v2 v3 v4 = du_inferOp_3258 v0 v1 v3 v4
du_inferOp_3258 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814 -> T_InferElabResult_814
du_inferOp_3258 v0 v1 v2 v3
  = case coe v3 of
      C_success_828 v4 v5 v6 v7 v8
        -> let v9
                 = coe
                     C_failure_830
                     (coe
                        ("Binary operator requires Int operands" :: Data.Text.Text)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Type.C_Int_60
                  -> coe
                       du_inferOp2_3274 (coe v1) (coe v5) (coe v6) (coe v8)
                       (coe
                          d_inferElabImpl_2542 (coe du_bumpFresh''_3246 (coe v0) (coe v7))
                          (coe v2))
                _ -> coe v9)
      C_failure_830 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferOp2
d_inferOp2_3274 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_inferOp2_3274 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
  = du_inferOp2_3274 v1 v4 v5 v7 v8
du_inferOp2_3274 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_814 -> T_InferElabResult_814
du_inferOp2_3274 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_828 v5 v6 v7 v8 v9
        -> let v10
                 = coe
                     C_failure_830
                     (coe
                        ("Binary operator requires Int operands" :: Data.Text.Text)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Once.Type.C_Int_60
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe MAlonzo.Code.Once.TypeCheck.Raw.d_isArithmeticOp_90 (coe v0))
                       (coe
                          C_success_828 (coe v5) (coe du_mkArithOp_3290 v0 v1 v6)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v2) (coe v7))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v3)
                             (coe v9)))
                       (coe
                          C_success_828
                          (coe
                             MAlonzo.Code.Once.Type.C__'43'__50
                             (coe MAlonzo.Code.Once.Type.C_Unit_44)
                             (coe MAlonzo.Code.Once.Type.C_Unit_44))
                          (coe du_mkCmpOp_3292 v0 v1 v6)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v2) (coe v7))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v3)
                             (coe v9)))
                _ -> coe v10)
      C_failure_830 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._._.mkArithOp
d_mkArithOp_3290 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_mkArithOp_3290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12
  = du_mkArithOp_3290 v12
du_mkArithOp_3290 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_mkArithOp_3290 v0
  = let v1 = coe MAlonzo.Code.Once.Surface.Syntax.C_add_308 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_add_308
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_sub_314
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_mul_320
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_div_326
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_mod''_332
         _ -> coe v1)
-- Once.TypeCheck.Elaborate._._._.mkCmpOp
d_mkCmpOp_3292 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_mkCmpOp_3292 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               v12
  = du_mkCmpOp_3292 v12
du_mkCmpOp_3292 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_mkCmpOp_3292 v0
  = let v1 = coe MAlonzo.Code.Once.Surface.Syntax.C_lt_344 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_lt_344
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_le_350
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_gt_356
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_ge_362
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_eq_368
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
           -> coe MAlonzo.Code.Once.Surface.Syntax.C_ne_374
         _ -> coe v1)
-- Once.TypeCheck.Elaborate._.inferNeg
d_inferNeg_3306 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_inferNeg_3306 ~v0 ~v1 v2 = du_inferNeg_3306 v2
du_inferNeg_3306 :: T_InferElabResult_814 -> T_InferElabResult_814
du_inferNeg_3306 v0
  = case coe v0 of
      C_success_828 v1 v2 v3 v4 v5
        -> let v6
                 = coe
                     C_failure_830
                     (coe ("Negation requires Int operand" :: Data.Text.Text)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Type.C_Int_60
                  -> coe
                       C_success_828 (coe v1)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_338 v2) (coe v3)
                       (coe v4) (coe v5)
                _ -> coe v6)
      C_failure_830 v1 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.extractInferResult
d_extractInferResult_3324 ::
  Integer ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_PolyInferResult_862 -> Maybe T_InferElabResult_814
d_extractInferResult_3324 v0 v1 v2 v3
  = case coe v3 of
      C_success_876 v4 v5 v6 v7 v8
        -> let v9 = MAlonzo.Code.Once.Type.d_extract_144 (coe v4) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                  -> let v11
                           = coe
                               MAlonzo.Code.Once.Surface.PolySyntax.d_unsafeCoerceExpr_324 v0 v1
                               v2 v4 v10 v5 in
                     coe
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe C_success_828 (coe v10) (coe v11) (coe v6) (coe v7) (coe v8)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_failure_830
                          (coe
                             ("Type contains unresolved type variables" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_878 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_failure_830 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.findPolyVarUsage
d_findPolyVarUsage_3426 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findPolyVarUsage_3426 v0 v1
  = let v2
          = coe
              du_go_2462 (coe v1) (coe d_named_1002 (coe v0))
              (coe d_polyCtx_1004 (coe v0)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Surface.PolySyntax.du_lookupPolyQuantity_38
                      (coe d_polyCtx_1004 (coe v0)) (coe v3)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.pzeroUsage
d_pzeroUsage_3448 ::
  Integer -> MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
d_pzeroUsage_3448 v0
  = coe MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60 (coe v0)
-- Once.TypeCheck.Elaborate.psingleUse
d_psingleUse_3452 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
d_psingleUse_3452 v0
  = coe MAlonzo.Code.Once.Surface.Syntax.d_singleUse_66 (coe v0)
-- Once.TypeCheck.Elaborate.ptailUsage
d_ptailUsage_3456 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
d_ptailUsage_3456 ~v0 = du_ptailUsage_3456
du_ptailUsage_3456 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
du_ptailUsage_3456
  = coe MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154
-- Once.TypeCheck.Elaborate.coercePolyExpr
d_coercePolyExpr_3466 ::
  Integer ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_PolyCheckResult_886
d_coercePolyExpr_3466 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_coercePolyExpr_3466 v2 v3 v4 v5 v6 v7
du_coercePolyExpr_3466 ::
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_PolyCheckResult_886
du_coercePolyExpr_3466 v0 v1 v2 v3 v4 v5
  = let v6 = d__'8799'PT__300 (coe v0) (coe v2) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe
                       seq (coe v8)
                       (coe C_success_900 (coe v1) (coe v3) (coe v4) (coe v5))
                else coe
                       seq (coe v8)
                       (coe
                          C_failure_902 (coe ("Type coercion failed" :: Data.Text.Text)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.coercePolyArg
d_coercePolyArg_3516
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate.coercePolyArg"
-- Once.TypeCheck.Elaborate.polyCheckImpl
d_polyCheckImpl_3522 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 -> T_PolyCheckResult_886
d_polyCheckImpl_3522 v0 v1 v2
  = let v3
          = let v3 = d_polyInferImpl_3526 (coe v0) (coe v1) in
            coe
              (case coe v3 of
                 C_success_876 v4 v5 v6 v7 v8
                   -> let v9 = d_matchesPolyType_570 (coe v2) (coe v4) in
                      coe
                        (case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                             -> coe
                                  du_coercePolyExpr_3466 (coe v4) (coe v5) (coe v2) (coe v6)
                                  (coe v7) (coe v8)
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> coe
                                  C_failure_902
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("Type mismatch: expected " :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v2))
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           (" but got " :: Data.Text.Text)
                                           (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v4)))))
                           _ -> MAlonzo.RTE.mazUnreachableError)
                 C_failure_878 v4 -> coe C_failure_902 (coe v4)
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v4 v5
           -> let v6 = d_polyInferImpl_3526 (coe v0) (coe v4) in
              coe
                (case coe v6 of
                   C_success_876 v7 v8 v9 v10 v11
                     -> let v12
                              = coe
                                  C_failure_902
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("Expected function type in application, got "
                                      ::
                                      Data.Text.Text)
                                     (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v7))) in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v13 v14 v15
                               -> coe
                                    du_checkArg_3632 (coe v0) (coe v13) (coe v14) (coe v15) (coe v8)
                                    (coe v9) (coe v10) (coe v11) (coe v5) (coe v2)
                                    (coe
                                       d_matchWithSubst_1322 (coe v2) (coe v15)
                                       (coe d_emptySubst_1198))
                             MAlonzo.Code.Once.Type.C_PEff_90 v13 v14
                               -> coe
                                    du_checkEffArg_3688 (coe v0) (coe v13) (coe v14) (coe v8)
                                    (coe v9) (coe v10) (coe v11) (coe v5) (coe v2)
                                    (coe
                                       d_matchWithSubst_1322 (coe v2) (coe v14)
                                       (coe d_emptySubst_1198))
                             _ -> coe v12)
                   C_failure_878 v7 -> coe C_failure_902 (coe v7)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v4 v5
           -> let v6
                    = coe
                        C_failure_902
                        (coe ("Lambda requires function type" :: Data.Text.Text)) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v7 v8 v9
                     -> let v10
                              = d_polyCheckImpl_3522
                                  (coe
                                     d_extendPolyNamedCtxPolyQ_1082 (coe v0) (coe v4) (coe v7)
                                     (coe v8))
                                  (coe v5) (coe v9) in
                        coe
                          (case coe v10 of
                             C_success_900 v11 v12 v13 v14
                               -> coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Once.Type.d__'8804'q__28
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140
                                          (coe v14) (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                       (coe v8))
                                    (coe
                                       C_success_900
                                       (coe MAlonzo.Code.Once.Surface.PolySyntax.C_plam_72 v11)
                                       (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                                       (coe du_ptailUsage_3456 v14))
                                    (coe
                                       C_failure_902
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("Parameter '" :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v4
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("' used with quantity " :: Data.Text.Text)
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   (MAlonzo.Code.Once.Type.d_showQuantity_30
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140
                                                         (coe v14)
                                                         (coe
                                                            MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      (" but declared with quantity "
                                                       ::
                                                       Data.Text.Text)
                                                      (MAlonzo.Code.Once.Type.d_showQuantity_30
                                                         (coe v8))))))))
                             C_failure_902 v11 -> coe v10
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v6)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.polyInferImpl
d_polyInferImpl_3526 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_PolyInferResult_862
d_polyInferImpl_3526 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> let v3
                 = coe
                     du_go_2326 (coe d_polyImports_1008 (coe v0)) (coe v2)
                     (coe d_size_1000 (coe v0)) (coe d_named_1002 (coe v0))
                     (coe d_polyCtx_1004 (coe v0)) (coe d_freshCounter_1006 (coe v0)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> let v9
                                         = coe
                                             du_go_2462 (coe v2) (coe d_named_1002 (coe v0))
                                             (coe d_polyCtx_1004 (coe v0)) in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                          -> let v11
                                                   = coe
                                                       MAlonzo.Code.Once.Surface.PolySyntax.du_lookupPolyQuantity_38
                                                       (coe d_polyCtx_1004 (coe v0)) (coe v10) in
                                             coe
                                               (coe
                                                  C_success_876 (coe v5) (coe v7)
                                                  (coe (0 :: Integer)) (coe v8)
                                                  (coe
                                                     d_psingleUse_3452 (d_size_1000 (coe v0)) v10
                                                     v11))
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> coe
                                                             C_success_876 (coe v5) (coe v7)
                                                             (coe (0 :: Integer)) (coe v8)
                                                             (coe
                                                                d_psingleUse_3452
                                                                (d_size_1000 (coe v0)) v11 v12)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe
                                                      C_success_876 (coe v5) (coe v7)
                                                      (coe (0 :: Integer)) (coe v8)
                                                      (coe
                                                         d_pzeroUsage_3448
                                                         (coe d_size_1000 (coe v0)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_878
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Unbound variable: " :: Data.Text.Text) v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> let v4
                 = coe
                     du_go_2326 (coe d_polyImports_1008 (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("." :: Data.Text.Text) v2))
                     (coe d_size_1000 (coe v0)) (coe d_named_1002 (coe v0))
                     (coe d_polyCtx_1004 (coe v0)) (coe d_freshCounter_1006 (coe v0)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> coe
                                     C_success_876 (coe v6) (coe v8) (coe (0 :: Integer)) (coe v9)
                                     (coe d_pzeroUsage_3448 (coe d_size_1000 (coe v0)))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_878
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Unbound qualified variable: " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("@" :: Data.Text.Text) v3)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v2 v3
        -> let v4 = d_polyInferImpl_3526 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_876 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_PUnit_80
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PVoid_82
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'42'__84 v10 v11
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'43'__86 v10 v11
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v10 v11 v12
                         -> coe
                              du_inferPolyArg_3926 (coe v0) (coe v10) (coe v11) (coe v12)
                              (coe v6) (coe v7) (coe v9)
                              (coe
                                 d_polyInferImpl_3526 (coe d_setPolyFresh_1054 (coe v0) (coe v8))
                                 (coe v3))
                       MAlonzo.Code.Once.Type.C_PEff_90 v10 v11
                         -> coe
                              du_inferPolyArgEff_3986 (coe v0) (coe v10) (coe v11) (coe v6)
                              (coe v7) (coe v9)
                              (coe
                                 d_polyInferImpl_3526 (coe d_setPolyFresh_1054 (coe v0) (coe v8))
                                 (coe v3))
                       MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v10
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_Pν'45'type_94 v10
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PInt_96
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PFloat_98
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PStr_100
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PBuffer_102
                         -> coe
                              C_failure_878
                              (coe ("Expected function type in application" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_TVar_104 v10
                         -> coe
                              C_failure_878
                              (coe
                                 ("Cannot apply type variable (need type annotation)"
                                  ::
                                  Data.Text.Text))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_878 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v2 v3
        -> coe
             C_failure_878
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Lambda without type annotation not supported in inference mode.\n"
                 ::
                 Data.Text.Text)
                ("Add a type annotation or use a type-annotated expression."
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v2 v3 v4
        -> let v5 = d_polyInferImpl_3526 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_876 v6 v7 v8 v9 v10
                  -> let v11
                           = d_polyInferImpl_3526
                               (coe
                                  d_extendPolyNamedCtxPoly_1066
                                  (coe d_setPolyFresh_1054 (coe v0) (coe v9)) (coe v2) (coe v6))
                               (coe v4) in
                     coe
                       (case coe v11 of
                          C_success_876 v12 v13 v14 v15 v16
                            -> coe
                                 C_success_876 (coe v12)
                                 (coe MAlonzo.Code.Once.Surface.PolySyntax.C_plet''_180 v6 v7 v13)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8)
                                    (coe addInt (coe (1 :: Integer)) (coe v14)))
                                 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v10)
                                    (coe du_ptailUsage_3456 v16))
                          C_failure_878 v12 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_878 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v2 v3
        -> let v4 = d_polyInferImpl_3526 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_876 v5 v6 v7 v8 v9
                  -> let v10
                           = d_polyInferImpl_3526
                               (coe d_setPolyFresh_1054 (coe v0) (coe v8)) (coe v3) in
                     coe
                       (case coe v10 of
                          C_success_876 v11 v12 v13 v14 v15
                            -> coe
                                 C_success_876
                                 (coe MAlonzo.Code.Once.Type.C__P'42'__84 (coe v5) (coe v11))
                                 (coe MAlonzo.Code.Once.Surface.PolySyntax.C_ppair_104 v6 v12)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v13))
                                 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v9)
                                    (coe v15))
                          C_failure_878 v11 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_878 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v2 v3 v4 v5 v6
        -> let v7 = d_polyInferImpl_3526 (coe v0) (coe v2) in
           coe
             (case coe v7 of
                C_success_876 v8 v9 v10 v11 v12
                  -> case coe v8 of
                       MAlonzo.Code.Once.Type.C_PUnit_80
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PVoid_82
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'42'__84 v13 v14
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'43'__86 v13 v14
                         -> coe
                              du_inferPolyLeft_4324 (coe v0) (coe v13) (coe v14) (coe v9)
                              (coe v10) (coe v12) (coe v5) (coe v6)
                              (coe
                                 d_polyInferImpl_3526
                                 (coe
                                    d_extendPolyNamedCtxPoly_1066
                                    (coe d_setPolyFresh_1054 (coe v0) (coe v11)) (coe v3) (coe v13))
                                 (coe v4))
                       MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v13 v14 v15
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PEff_90 v13 v14
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v13
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_Pν'45'type_94 v13
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PInt_96
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PFloat_98
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PStr_100
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PBuffer_102
                         -> coe
                              C_failure_878 (coe ("Expected sum type in case" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_TVar_104 v13
                         -> coe
                              C_failure_878
                              (coe ("Cannot case on type variable" :: Data.Text.Text))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_878 v8 -> coe v7
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe
             C_success_876 (coe MAlonzo.Code.Once.Type.C_PUnit_80)
             (coe MAlonzo.Code.Once.Surface.PolySyntax.C_punit_162)
             (coe (0 :: Integer)) (coe d_freshCounter_1006 (coe v0))
             (coe d_pzeroUsage_3448 (coe d_size_1000 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v2
        -> coe
             C_success_876 (coe MAlonzo.Code.Once.Type.C_PInt_96)
             (coe MAlonzo.Code.Once.Surface.PolySyntax.C_pint_186 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_1006 (coe v0))
             (coe d_pzeroUsage_3448 (coe d_size_1000 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v2
        -> coe
             C_success_876 (coe MAlonzo.Code.Once.Type.C_PStr_100)
             (coe MAlonzo.Code.Once.Surface.PolySyntax.C_pstr_192 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_1006 (coe v0))
             (coe d_pzeroUsage_3448 (coe d_size_1000 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v2 v3
        -> coe d_polyInferImpl_3526 (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v2 v3 v4
        -> let v5 = d_polyInferImpl_3526 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_876 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_PUnit_80
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PVoid_82
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'42'__84 v11 v12
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'43'__86 v11 v12
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v11 v12 v13
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PEff_90 v11 v12
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v11
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_Pν'45'type_94 v11
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PInt_96
                         -> coe
                              du_checkOp2_4580 (coe v7) (coe v8) (coe v10) (coe v2)
                              (coe
                                 d_polyInferImpl_3526 (coe d_setPolyFresh_1054 (coe v0) (coe v9))
                                 (coe v4))
                       MAlonzo.Code.Once.Type.C_PFloat_98
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PStr_100
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PBuffer_102
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_TVar_104 v11
                         -> coe
                              C_failure_878
                              (coe ("Binary operator requires Int operands" :: Data.Text.Text))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_878 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v3
        -> let v4 = d_polyInferImpl_3526 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                C_success_876 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_PUnit_80
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PVoid_82
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'42'__84 v10 v11
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'43'__86 v10 v11
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v10 v11 v12
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PEff_90 v10 v11
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v10
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_Pν'45'type_94 v10
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PInt_96
                         -> coe
                              C_success_876 (coe v5)
                              (coe MAlonzo.Code.Once.Surface.PolySyntax.C_pneg_228 v6) (coe v7)
                              (coe v8) (coe v9)
                       MAlonzo.Code.Once.Type.C_PFloat_98
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PStr_100
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_PBuffer_102
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       MAlonzo.Code.Once.Type.C_TVar_104 v10
                         -> coe
                              C_failure_878
                              (coe ("Negation requires Int operand" :: Data.Text.Text))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_878 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.checkArg
d_checkArg_3632 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_PolyCheckResult_886
d_checkArg_3632 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_checkArg_3632 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_checkArg_3632 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_PolyCheckResult_886
du_checkArg_3632 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
        -> case coe v11 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
               -> coe
                    du_checkArgWithResolvedType_3640 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe d_applySubst_1240 (coe v13) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_902
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Result type mismatch: expected " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v9))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (" but function returns " :: Data.Text.Text)
                      (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v3)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.checkArgWithResolvedType
d_checkArgWithResolvedType_3640 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_70 -> T_PolyCheckResult_886
d_checkArgWithResolvedType_3640 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                ~v11 ~v12 v13
  = du_checkArgWithResolvedType_3640
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v13
du_checkArgWithResolvedType_3640 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 -> T_PolyCheckResult_886
du_checkArgWithResolvedType_3640 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = let v11
          = d_polyCheckImpl_3522
              (coe d_setPolyFresh_1054 (coe v0) (coe v6)) (coe v8) (coe v10) in
    coe
      (case coe v11 of
         C_success_900 v12 v13 v14 v15
           -> coe
                C_success_900
                (coe
                   d_coercePolyArg_3516 (d_size_1000 (coe v0))
                   (d_polyCtx_1004 (coe v0)) v9 v3
                   (coe
                      MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84 v1 v2 v4
                      (coe
                         d_coercePolyArg_3516 (d_size_1000 (coe v0))
                         (d_polyCtx_1004 (coe v0)) v1 v10 v12)))
                (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v5) (coe v13))
                (coe v14)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v7)
                   (coe v15))
         C_failure_902 v12 -> coe v11
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate._.checkEffArg
d_checkEffArg_3688 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_PolyCheckResult_886
d_checkEffArg_3688 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_checkEffArg_3688 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_checkEffArg_3688 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_PolyCheckResult_886
du_checkEffArg_3688 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> case coe v10 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> coe
                    du_checkArgWithResolvedType_3696 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe d_applySubst_1240 (coe v12) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_902
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Effect result type mismatch: expected " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v8))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (" but effect returns " :: Data.Text.Text)
                      (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v2)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.checkArgWithResolvedType
d_checkArgWithResolvedType_3696 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_70 -> T_PolyCheckResult_886
d_checkArgWithResolvedType_3696 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
                                ~v11 v12
  = du_checkArgWithResolvedType_3696 v0 v2 v3 v4 v5 v6 v7 v8 v9 v12
du_checkArgWithResolvedType_3696 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 -> T_PolyCheckResult_886
du_checkArgWithResolvedType_3696 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = d_polyCheckImpl_3522
              (coe d_setPolyFresh_1054 (coe v0) (coe v5)) (coe v7) (coe v9) in
    coe
      (case coe v10 of
         C_success_900 v11 v12 v13 v14
           -> coe
                C_success_900
                (coe
                   d_coercePolyArg_3516 (d_size_1000 (coe v0))
                   (d_polyCtx_1004 (coe v0)) v8 v2
                   (coe
                      MAlonzo.Code.Once.Surface.PolySyntax.C_peffApp_94 v1 v3
                      (coe
                         d_coercePolyArg_3516 (d_size_1000 (coe v0))
                         (d_polyCtx_1004 (coe v0)) v1 v9 v11)))
                (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v4) (coe v12))
                (coe v13)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v6)
                   (coe v14))
         C_failure_902 v11 -> coe v10
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate._.inferPolyArg
d_inferPolyArg_3926 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
d_inferPolyArg_3926 v0 ~v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9 v10
  = du_inferPolyArg_3926 v0 v2 v3 v4 v5 v6 v8 v10
du_inferPolyArg_3926 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
du_inferPolyArg_3926 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_success_876 v8 v9 v10 v11 v12
        -> let v13 = d_matchesPolyType_570 (coe v1) (coe v8) in
           coe
             (case coe v13 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                  -> coe
                       C_success_876 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Surface.PolySyntax.C_papp_84 v1 v2 v4
                          (coe
                             d_coercePolyArg_3516 (d_size_1000 (coe v0))
                             (d_polyCtx_1004 (coe v0)) v1 v8 v9))
                       (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v5) (coe v10))
                       (coe v11)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v6)
                          (coe v12))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_878
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Type mismatch in application: expected " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v1))
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (" but got " :: Data.Text.Text)
                                (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v8)))))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_878 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferPolyArgEff
d_inferPolyArgEff_3986 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
d_inferPolyArgEff_3986 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9
  = du_inferPolyArgEff_3986 v0 v2 v3 v4 v5 v7 v9
du_inferPolyArgEff_3986 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
du_inferPolyArgEff_3986 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_success_876 v7 v8 v9 v10 v11
        -> let v12 = d_matchesPolyType_570 (coe v1) (coe v7) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                  -> coe
                       C_success_876 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Surface.PolySyntax.C_peffApp_94 v1 v3
                          (coe
                             d_coercePolyArg_3516 (d_size_1000 (coe v0))
                             (d_polyCtx_1004 (coe v0)) v1 v7 v8))
                       (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v4) (coe v9))
                       (coe v10)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v5)
                          (coe v11))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_878
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Type mismatch in effect application: expected "
                           ::
                           Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v1))
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (" but got " :: Data.Text.Text)
                                (MAlonzo.Code.Once.Type.d_showPolyType_404 (coe v7)))))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_878 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferPolyLeft
d_inferPolyLeft_4324 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
d_inferPolyLeft_4324 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 v12
  = du_inferPolyLeft_4324 v0 v2 v3 v4 v5 v7 v10 v11 v12
du_inferPolyLeft_4324 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
du_inferPolyLeft_4324 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_success_876 v9 v10 v11 v12 v13
        -> coe
             du_inferPolyRight_4342 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v9) (coe v10) (coe v11) (coe v13)
             (coe
                d_polyInferImpl_3526
                (coe
                   d_extendPolyNamedCtxPoly_1066
                   (coe d_setPolyFresh_1054 (coe v0) (coe v12)) (coe v6) (coe v2))
                (coe v7))
      C_failure_878 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferPolyRight
d_inferPolyRight_4342 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
d_inferPolyRight_4342 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
                      v12 v13 v14 ~v15 v16 v17
  = du_inferPolyRight_4342 v0 v2 v3 v4 v5 v7 v12 v13 v14 v16 v17
du_inferPolyRight_4342 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
du_inferPolyRight_4342 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_success_876 v11 v12 v13 v14 v15
        -> let v16 = d_matchesPolyType_570 (coe v6) (coe v11) in
           coe
             (case coe v16 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                  -> coe
                       C_success_876 (coe v6)
                       (coe
                          MAlonzo.Code.Once.Surface.PolySyntax.C_pcase''_156 v1 v2 v3 v7
                          (coe
                             d_coercePolyArg_3516
                             (addInt (coe (1 :: Integer)) (coe d_size_1000 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.PolySyntax.du__P'44'__16
                                (coe d_polyCtx_1004 (coe v0)) (coe v2))
                             v6 v11 v12))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                          (coe
                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v4)
                             (coe addInt (coe (1 :: Integer)) (coe v8)))
                          (coe addInt (coe (1 :: Integer)) (coe v13)))
                       (coe v14)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v5)
                             (coe du_ptailUsage_3456 v9))
                          (coe du_ptailUsage_3456 v15))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_878
                       (coe ("Case branches have different types" :: Data.Text.Text))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_878 v11 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.checkOp2
d_checkOp2_4580 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
d_checkOp2_4580 ~v0 ~v1 v2 v3 ~v4 v5 v6 ~v7 v8
  = du_checkOp2_4580 v2 v3 v5 v6 v8
du_checkOp2_4580 ::
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  T_PolyInferResult_862 -> T_PolyInferResult_862
du_checkOp2_4580 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_876 v5 v6 v7 v8 v9
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C_PUnit_80
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_PVoid_82
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__P'42'__84 v10 v11
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__P'43'__86 v10 v11
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__88 v10 v11 v12
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_PEff_90 v10 v11
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Pμ'45'type_92 v10
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Pν'45'type_94 v10
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_PInt_96
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe MAlonzo.Code.Once.TypeCheck.Raw.d_isArithmeticOp_90 (coe v3))
                    (coe
                       C_success_876 (coe v5) (coe du_mkPolyArithOp_4596 v3 v0 v6)
                       (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v1) (coe v7))
                       (coe v8)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v2)
                          (coe v9)))
                    (coe
                       C_success_876
                       (coe
                          MAlonzo.Code.Once.Type.C__P'43'__86
                          (coe MAlonzo.Code.Once.Type.C_PUnit_80)
                          (coe MAlonzo.Code.Once.Type.C_PUnit_80))
                       (coe du_mkPolyCmpOp_4598 v3 v0 v6)
                       (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v1) (coe v7))
                       (coe v8)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v2)
                          (coe v9)))
             MAlonzo.Code.Once.Type.C_PFloat_98
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_PStr_100
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_PBuffer_102
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_TVar_104 v10
               -> coe
                    C_failure_878
                    (coe ("Binary operator requires Int operands" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_878 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.mkPolyArithOp
d_mkPolyArithOp_4596 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52
d_mkPolyArithOp_4596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12
  = du_mkPolyArithOp_4596 v12
du_mkPolyArithOp_4596 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52
du_mkPolyArithOp_4596 v0
  = let v1 = coe MAlonzo.Code.Once.Surface.PolySyntax.C_padd_198 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_padd_198
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_psub_204
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_pmul_210
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_pdiv_216
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_pmod''_222
         _ -> coe v1)
-- Once.TypeCheck.Elaborate._._.mkPolyCmpOp
d_mkPolyCmpOp_4598 ::
  T_PolyNamedCtx_988 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52
d_mkPolyCmpOp_4598 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 v12
  = du_mkPolyCmpOp_4598 v12
du_mkPolyCmpOp_4598 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyExpr_52
du_mkPolyCmpOp_4598 v0
  = let v1 = coe MAlonzo.Code.Once.Surface.PolySyntax.C_plt_234 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_plt_234
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_ple_240
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_pgt_246
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_pge_252
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_peq_258
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
           -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_pne_264
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.namedToPolyCtx
d_namedToPolyCtx_4774 :: T_NamedCtx_908 -> T_PolyNamedCtx_988
d_namedToPolyCtx_4774 v0
  = case coe v0 of
      C_mkCtx_930 v1 v2 v3 v4 v5
        -> coe
             C_mkPolyCtx_1010 (coe v1) (coe v2) (coe du_embedSCtx_4792 (coe v3))
             (coe v4) (coe d_embedImports_980 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.embedSCtx
d_embedSCtx_4792 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6
d_embedSCtx_4792 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_embedSCtx_4792 v6
du_embedSCtx_4792 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6
du_embedSCtx_4792 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
        -> coe MAlonzo.Code.Once.Surface.PolySyntax.C_P'8709'_8
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Surface.PolySyntax.C__P'44'_'94'__12
             (coe du_embedSCtx_4792 (coe v2))
             (MAlonzo.Code.Once.Type.d_embed_108 (coe v3)) v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_4802 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814
d_inferElab_4802 v0 v1
  = coe
      du_tryPolyInfer_4850 (coe v0)
      (coe
         d_polyInferImpl_3526 (coe d_namedToPolyCtx_4774 (coe v0)) (coe v1))
-- Once.TypeCheck.Elaborate._.checkDepth
d_checkDepth_4812 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_814 -> T_InferElabResult_814
d_checkDepth_4812 ~v0 ~v1 v2 = du_checkDepth_4812 v2
du_checkDepth_4812 ::
  T_InferElabResult_814 -> T_InferElabResult_814
du_checkDepth_4812 v0
  = case coe v0 of
      C_success_828 v1 v2 v3 v4 v5
        -> let v6
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     (\ v6 ->
                        coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                          (coe v3))
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                        (coe
                           MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v3)
                           (coe (7 :: Integer)))) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe v0)
                       else coe
                              seq (coe v8)
                              (coe
                                 C_failure_830
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("Expression nesting depth exceeds verified limit.\n"
                                     ::
                                     Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("  Depth encountered: " :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("\n" :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("  Proven depth limit: 7\n" :: Data.Text.Text)
                                                ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                 ::
                                                 Data.Text.Text)))))))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_830 v1 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.tryPolyInfer
d_tryPolyInfer_4850 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_PolyInferResult_862 -> T_InferElabResult_814
d_tryPolyInfer_4850 v0 ~v1 v2 = du_tryPolyInfer_4850 v0 v2
du_tryPolyInfer_4850 ::
  T_NamedCtx_908 -> T_PolyInferResult_862 -> T_InferElabResult_814
du_tryPolyInfer_4850 v0 v1
  = let v2
          = d_extractInferResult_3324
              (coe d_size_920 (coe v0))
              (coe d_polyCtx_1004 (coe d_namedToPolyCtx_4774 (coe v0)))
              (coe d_debruijn_924 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_checkDepth_4812 (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                C_failure_830
                (coe
                   ("Internal error: extraction returned nothing" :: Data.Text.Text))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.extractCheckResult
d_extractCheckResult_4876 ::
  Integer ->
  MAlonzo.Code.Once.Surface.PolySyntax.T_PolyCtx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  T_PolyCheckResult_886 -> Maybe T_CheckElabResult_838
d_extractCheckResult_4876 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_900 v6 v7 v8 v9
        -> let v10
                 = coe
                     MAlonzo.Code.Once.Surface.PolySyntax.d_unsafeCoerceExpr_324 v0 v1
                     v2 v3 v4 v6 in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe C_success_852 (coe v10) (coe v7) (coe v8) (coe v9)))
      C_failure_902 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_failure_854 (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_4926 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_CheckElabResult_838
d_checkElab_4926 v0 v1 v2
  = coe
      du_tryPolyCheck_4970 (coe v0) (coe v2)
      (coe
         d_polyCheckImpl_3522 (coe d_namedToPolyCtx_4774 (coe v0)) (coe v1)
         (coe MAlonzo.Code.Once.Type.d_embed_108 (coe v2)))
-- Once.TypeCheck.Elaborate._.checkDepth
d_checkDepth_4938 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  T_CheckElabResult_838 -> T_CheckElabResult_838
d_checkDepth_4938 ~v0 ~v1 ~v2 v3 = du_checkDepth_4938 v3
du_checkDepth_4938 ::
  T_CheckElabResult_838 -> T_CheckElabResult_838
du_checkDepth_4938 v0
  = case coe v0 of
      C_success_852 v1 v2 v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     (\ v5 ->
                        coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                          (coe v2))
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                        (coe
                           MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v2)
                           (coe (7 :: Integer)))) in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then coe seq (coe v7) (coe v0)
                       else coe
                              seq (coe v7)
                              (coe
                                 C_failure_854
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("Expression nesting depth exceeds verified limit.\n"
                                     ::
                                     Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("  Depth encountered: " :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("\n" :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("  Proven depth limit: 7\n" :: Data.Text.Text)
                                                ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                 ::
                                                 Data.Text.Text)))))))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_854 v1 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.tryPolyCheck
d_tryPolyCheck_4970 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  T_PolyCheckResult_886 -> T_CheckElabResult_838
d_tryPolyCheck_4970 v0 ~v1 v2 v3 = du_tryPolyCheck_4970 v0 v2 v3
du_tryPolyCheck_4970 ::
  T_NamedCtx_908 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  T_PolyCheckResult_886 -> T_CheckElabResult_838
du_tryPolyCheck_4970 v0 v1 v2
  = let v3
          = d_extractCheckResult_4876
              (coe d_size_920 (coe v0))
              (coe d_polyCtx_1004 (coe d_namedToPolyCtx_4774 (coe v0)))
              (coe d_debruijn_924 (coe v0))
              (coe MAlonzo.Code.Once.Type.d_embed_108 (coe v1)) (coe v1)
              (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe du_checkDepth_4938 (coe v4)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                C_failure_854
                (coe
                   ("Internal error: extraction returned nothing" :: Data.Text.Text))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExprTyped
d_compileExprTyped_4990 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_12
d_compileExprTyped_4990 v0 v1
  = let v2
          = d_extractCheckResult_4876
              (coe d_size_920 (coe d_emptyCtx_932))
              (coe
                 d_polyCtx_1004 (coe d_namedToPolyCtx_4774 (coe d_emptyCtx_932)))
              (coe d_debruijn_924 (coe d_emptyCtx_932))
              (coe MAlonzo.Code.Once.Type.d_embed_108 (coe v1)) (coe v1)
              (coe
                 d_polyCheckImpl_3522
                 (coe d_namedToPolyCtx_4774 (coe d_emptyCtx_932)) (coe v0)
                 (coe MAlonzo.Code.Once.Type.d_embed_108 (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> let v4 = coe du_checkDepth_4938 (coe v3) in
              coe
                (case coe v4 of
                   C_success_852 v5 v6 v7 v8
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                             (coe (0 :: Integer))
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v1)
                             (coe v5))
                   C_failure_854 v5
                     -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExpr
d_compileExpr_5012 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_5012 v0
  = let v1
          = d_extractInferResult_3324
              (coe d_size_920 (coe d_emptyCtx_932))
              (coe
                 d_polyCtx_1004 (coe d_namedToPolyCtx_4774 (coe d_emptyCtx_932)))
              (coe d_debruijn_924 (coe d_emptyCtx_932))
              (coe
                 d_polyInferImpl_3526
                 (coe d_namedToPolyCtx_4774 (coe d_emptyCtx_932)) (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> let v3 = coe du_checkDepth_4812 (coe v2) in
              coe
                (case coe v3 of
                   C_success_828 v4 v5 v6 v7 v8
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v4)
                                (coe v5)))
                   C_failure_830 v4
                     -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
