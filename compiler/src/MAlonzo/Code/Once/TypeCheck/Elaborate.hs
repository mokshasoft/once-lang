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
             MAlonzo.Code.Once.Type.C_TVar_68 v2
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
             MAlonzo.Code.Once.Type.C_TVar_68 v2
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
             MAlonzo.Code.Once.Type.C_TVar_68 v4
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
             MAlonzo.Code.Once.Type.C_TVar_68 v4
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
             MAlonzo.Code.Once.Type.C_TVar_68 v5
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
             MAlonzo.Code.Once.Type.C_TVar_68 v4
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
             MAlonzo.Code.Once.Type.C_TVar_68 v3
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
             MAlonzo.Code.Once.Type.C_TVar_68 v3
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
             MAlonzo.Code.Once.Type.C_TVar_68 v2
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
             MAlonzo.Code.Once.Type.C_TVar_68 v2
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
             MAlonzo.Code.Once.Type.C_TVar_68 v2
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
             MAlonzo.Code.Once.Type.C_TVar_68 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_TVar_68 v2
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
             MAlonzo.Code.Once.Type.C_TVar_68 v3
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
-- Once.TypeCheck.Elaborate.InferElabResult
d_InferElabResult_314 a0 a1 = ()
data T_InferElabResult_314
  = C_success_328 MAlonzo.Code.Once.Type.T_Type_34
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 Integer Integer
                  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 |
    C_failure_330 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_338 a0 a1 a2 = ()
data T_CheckElabResult_338
  = C_success_352 MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 Integer
                  Integer MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 |
    C_failure_354 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.Imports
d_Imports_356 :: ()
d_Imports_356 = erased
-- Once.TypeCheck.Elaborate.emptyImports
d_emptyImports_358 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyImports_358
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Elaborate.NamedCtx
d_NamedCtx_360 = ()
data T_NamedCtx_360
  = C_mkCtx_382 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 Integer
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Elaborate.NamedCtx.size
d_size_372 :: T_NamedCtx_360 -> Integer
d_size_372 v0
  = case coe v0 of
      C_mkCtx_382 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.named
d_named_374 ::
  T_NamedCtx_360 -> [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_374 v0
  = case coe v0 of
      C_mkCtx_382 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.debruijn
d_debruijn_376 ::
  T_NamedCtx_360 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_376 v0
  = case coe v0 of
      C_mkCtx_382 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.freshCounter
d_freshCounter_378 :: T_NamedCtx_360 -> Integer
d_freshCounter_378 v0
  = case coe v0 of
      C_mkCtx_382 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.imports
d_imports_380 ::
  T_NamedCtx_360 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_380 v0
  = case coe v0 of
      C_mkCtx_382 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.emptyCtx
d_emptyCtx_384 :: T_NamedCtx_360
d_emptyCtx_384
  = coe
      C_mkCtx_382 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe d_emptyImports_358)
-- Once.TypeCheck.Elaborate.ctxWithImports
d_ctxWithImports_386 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_360
d_ctxWithImports_386 v0
  = coe
      C_mkCtx_382 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0)
-- Once.TypeCheck.Elaborate.ctxWithImportsAndSelf
d_ctxWithImportsAndSelf_390 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_NamedCtx_360
d_ctxWithImportsAndSelf_390 v0 v1 v2
  = coe
      d_ctxWithImports_386
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
         (coe v0))
-- Once.TypeCheck.Elaborate.extendNamedCtx
d_extendNamedCtx_398 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_NamedCtx_360
d_extendNamedCtx_398 v0 v1 v2
  = case coe v0 of
      C_mkCtx_382 v3 v4 v5 v6 v7
        -> coe
             C_mkCtx_382 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v5) (coe v2))
             (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.bumpFresh
d_bumpFresh_414 :: T_NamedCtx_360 -> T_NamedCtx_360
d_bumpFresh_414 v0
  = case coe v0 of
      C_mkCtx_382 v1 v2 v3 v4 v5
        -> coe
             C_mkCtx_382 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.freshTVar
d_freshTVar_426 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_426 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Elaborate.findVarIndex
d_findVarIndex_432 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_findVarIndex_432 v0 v1
  = case coe v0 of
      C_mkCtx_382 v2 v3 v4 v5 v6
        -> coe du_go_454 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_454 ::
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
d_go_454 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 = du_go_454 v5 v7 v8
du_go_454 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_go_454 v0 v1 v2
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
                                     (let v12 = coe du_go_454 (coe v0) (coe v4) (coe v6) in
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
d_Subst_526 :: ()
d_Subst_526 = erased
-- Once.TypeCheck.Elaborate.emptySubst
d_emptySubst_528 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptySubst_528 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Elaborate.extendSubst
d_extendSubst_530 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_530 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.TypeCheck.Elaborate.lookupSubst
d_lookupSubst_538 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_34
d_lookupSubst_538 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupSubst_538 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.applySubstF'
d_applySubstF''_568 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Functor_32 ->
  MAlonzo.Code.Once.Type.T_Functor_32
d_applySubstF''_568 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_36 v2
        -> coe
             MAlonzo.Code.Once.Type.C_K_36
             (coe d_applySubst_570 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Id_38 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__40 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'8853'__40
             (coe d_applySubstF''_568 (coe v0) (coe v2))
             (coe d_applySubstF''_568 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8855'__42 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'8855'__42
             (coe d_applySubstF''_568 (coe v0) (coe v2))
             (coe d_applySubstF''_568 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.applySubst
d_applySubst_570 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34
d_applySubst_570 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_44 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_46 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__48 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__48
             (coe d_applySubst_570 (coe v0) (coe v2))
             (coe d_applySubst_570 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'43'__50 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__50
             (coe d_applySubst_570 (coe v0) (coe v2))
             (coe d_applySubst_570 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52
             (coe d_applySubst_570 (coe v0) (coe v2)) (coe v3)
             (coe d_applySubst_570 (coe v0) (coe v4))
      MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C_Eff_54
             (coe d_applySubst_570 (coe v0) (coe v2))
             (coe d_applySubst_570 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C_μ'45'type_56 v2
        -> coe
             MAlonzo.Code.Once.Type.C_μ'45'type_56
             (coe d_applySubstF''_568 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_ν'45'type_58 v2
        -> coe
             MAlonzo.Code.Once.Type.C_ν'45'type_58
             (coe d_applySubstF''_568 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Int_60 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_62 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_64 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_66 -> coe v1
      MAlonzo.Code.Once.Type.C_TVar_68 v2
        -> let v3 = d_lookupSubst_538 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v4
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.instantiate
d_instantiate_652 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instantiate_652 v0 v1
  = coe du_go_662 (coe v0) (coe v1) (coe d_emptySubst_528)
-- Once.TypeCheck.Elaborate._.go
d_go_662 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_662 ~v0 ~v1 v2 v3 v4 = du_go_662 v2 v3 v4
du_go_662 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_662 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_44
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Void_46
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C__'42'__48 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_662 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_662 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C__'43'__50 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__'43'__50
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_662 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_662 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_662 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_662 (coe v5)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C_Eff_54 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C_Eff_54
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_662 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_662 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_662 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C_μ'45'type_56 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_ν'45'type_58 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Int_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Float_62
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Str_64
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Buffer_66
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_TVar_68 v3
        -> let v4 = d_lookupSubst_538 (coe v2) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v1)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.builtinType
d_builtinType_796 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_builtinType_796 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         l | (==) l ("apply" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__48
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__76
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_68
                        (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_app_194
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_fst''_224
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_snd''_234
                              (MAlonzo.Code.Once.Type.d__'8658'__76
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_68
                                    (coe
                                       d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("arr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__76
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.C_Eff_54
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_arr''_384
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("case" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__76
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__76
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__76
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe d_freshTVar_426 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__76
                           (coe
                              MAlonzo.Code.Once.Type.C__'43'__50
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_68
                                 (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe
                                 d_freshTVar_426 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_case''_266
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_68
                                    (coe
                                       d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_194
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_68
                                       (coe d_freshTVar_426 (coe v1)))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe
                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                             (coe
                                                MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_194
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_68
                                       (coe
                                          d_freshTVar_426
                                          (coe addInt (coe (1 :: Integer)) (coe v1))))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe
                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                     (coe addInt (coe (3 :: Integer)) (coe v1))))
         l | (==) l ("compose" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__76
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__76
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__76
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__76
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe
                                 d_freshTVar_426 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_app_194
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_68
                                    (coe
                                       d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))
                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_194
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_68
                                       (coe d_freshTVar_426 (coe v1)))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                     (coe addInt (coe (3 :: Integer)) (coe v1))))
         l | (==) l ("curry" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__76
                        (coe
                           MAlonzo.Code.Once.Type.C__'42'__48
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__76
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__76
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe
                                 d_freshTVar_426 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_app_194
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'42'__48
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_68
                                       (coe d_freshTVar_426 (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_68
                                       (coe
                                          d_freshTVar_426
                                          (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_pair_214
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                     (coe addInt (coe (3 :: Integer)) (coe v1))))
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__48
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fst''_224
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("id" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_170
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                     (coe addInt (coe (1 :: Integer)) (coe v1))))
         l | (==) l ("initial" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe MAlonzo.Code.Once.Type.C_Void_46)
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_absurd_280
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (1 :: Integer)) (coe v1))))
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.Type.C__'43'__50
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_inl''_244
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_68
                        (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))
                     (coe
                        MAlonzo.Code.Once.Type.C__'43'__50
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_inr''_254
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__76
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__76
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__76
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68
                              (coe d_freshTVar_426 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__76
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C__'42'__48
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_68
                                 (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_68
                                 (coe
                                    d_freshTVar_426 (coe addInt (coe (2 :: Integer)) (coe v1))))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_pair_214
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_194
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_68
                                       (coe d_freshTVar_426 (coe v1)))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe
                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_194
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_68
                                       (coe d_freshTVar_426 (coe v1)))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                     (coe addInt (coe (3 :: Integer)) (coe v1))))
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__48
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68
                           (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_68
                        (coe d_freshTVar_426 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_snd''_234
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("terminal" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__76
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_68 (coe d_freshTVar_426 (coe v1)))
                     (coe MAlonzo.Code.Once.Type.C_Unit_44))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_182
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_272))
                     (coe addInt (coe (1 :: Integer)) (coe v1))))
         l | (==) l ("unit" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Type.C_Unit_44)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_272) (coe v1)))
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.lookupImport
d_lookupImport_880 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_34
d_lookupImport_880 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupImport_880 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.lookupVar
d_lookupVar_914 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupVar_914 v0 v1
  = case coe v0 of
      C_mkCtx_382 v2 v3 v4 v5 v6
        -> coe
             du_go_938 (coe v6) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_938 ::
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
d_go_938 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_go_938 v4 v5 v6 v7 v8 v9
du_go_938 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_938 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      []
        -> case coe v4 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> let v6 = d_builtinType_796 (coe v1) (coe v5) in
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
                                                     d_weakenFromEmpty_12 (coe (0 :: Integer))
                                                     (coe v4) (coe v8) (coe v10))
                                                  (coe v11)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> let v7 = d_lookupImport_880 (coe v0) (coe v1) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Once.Surface.Syntax.C_prim_392 v1)
                                              (coe v5)))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                 _ -> MAlonzo.RTE.mazUnreachableError)
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
                                                           du_go_938 (coe v0) (coe v1) (coe v12)
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
                                                             du_go_938 (coe v0) (coe v1) (coe v12)
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
-- Once.TypeCheck.Elaborate.checkElabImpl
d_checkElabImpl_1128 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_CheckElabResult_338
d_checkElabImpl_1128 v0 v1 v2
  = let v3
          = let v3 = d_inferElabImpl_1132 (coe v0) (coe v1) in
            coe
              (case coe v3 of
                 C_success_328 v4 v5 v6 v7 v8
                   -> let v9 = d__'8799'T__40 (coe v4) (coe v2) in
                      coe
                        (case coe v9 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                             -> if coe v10
                                  then coe
                                         seq (coe v11)
                                         (coe C_success_352 (coe v5) (coe v6) (coe v7) (coe v8))
                                  else coe
                                         seq (coe v11)
                                         (coe
                                            C_failure_354
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               ("Type mismatch: expected " :: Data.Text.Text)
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  (MAlonzo.Code.Once.Type.d_showType_130 (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                     (" but got " :: Data.Text.Text)
                                                     (MAlonzo.Code.Once.Type.d_showType_130
                                                        (coe v4))))))
                           _ -> MAlonzo.RTE.mazUnreachableError)
                 C_failure_330 v4 -> coe C_failure_354 (coe v4)
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v4 v5
           -> let v6
                    = coe
                        C_failure_354
                        (coe ("Lambda requires function type" :: Data.Text.Text)) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v7 v8 v9
                     -> let v10
                              = d_checkElabImpl_1128
                                  (coe d_extendNamedCtx_398 (coe v0) (coe v4) (coe v7)) (coe v5)
                                  (coe v9) in
                        coe
                          (case coe v10 of
                             C_success_352 v11 v12 v13 v14
                               -> coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Once.Type.d__'8804'q__28
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140
                                          (coe v14) (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                       (coe v8))
                                    (coe
                                       C_success_352
                                       (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_182 v11)
                                       (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154
                                          (coe v14)))
                                    (coe
                                       C_failure_354
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
                             C_failure_354 v11 -> coe v10
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v6)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.inferElabImpl
d_inferElabImpl_1132 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_314
d_inferElabImpl_1132 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> let v3
                 = coe
                     du_go_938 (coe d_imports_380 (coe v0)) (coe v2)
                     (coe d_size_372 (coe v0)) (coe d_named_374 (coe v0))
                     (coe d_debruijn_376 (coe v0)) (coe d_freshCounter_378 (coe v0)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> let v9
                                         = coe
                                             du_go_454 (coe v2) (coe d_named_374 (coe v0))
                                             (coe d_debruijn_376 (coe v0)) in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                          -> coe
                                               C_success_328 (coe v5) (coe v7) (coe (0 :: Integer))
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.d_singleUse_66
                                                  (coe d_size_372 (coe v0)) (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.du_lookupQuantity_38
                                                     (coe d_debruijn_376 (coe v0)) (coe v10)))
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> coe
                                               C_success_328 (coe v5) (coe v7) (coe (0 :: Integer))
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                  (coe d_size_372 (coe v0)))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_330
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Unbound variable: " :: Data.Text.Text) v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> let v4
                 = coe
                     du_go_938 (coe d_imports_380 (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("." :: Data.Text.Text) v2))
                     (coe d_size_372 (coe v0)) (coe d_named_374 (coe v0))
                     (coe d_debruijn_376 (coe v0)) (coe d_freshCounter_378 (coe v0)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> coe
                                     C_success_328 (coe v6) (coe v8) (coe (0 :: Integer)) (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                        (coe d_size_372 (coe v0)))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_330
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
             du_inferApp_1384 (coe v0) (coe v3)
             (coe d_inferElabImpl_1132 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v2 v3
        -> let v4
                 = d_inferElabImpl_1132
                     (coe
                        d_extendNamedCtx_398 (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_68 (coe ("\945" :: Data.Text.Text))))
                     (coe v3) in
           coe
             (case coe v4 of
                C_success_328 v5 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.Type.d__'8804'q__28
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140 (coe v9)
                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe
                          C_success_328
                          (coe
                             MAlonzo.Code.Once.Type.d__'8658'__76
                             (coe
                                MAlonzo.Code.Once.Type.C_TVar_68 (coe ("\945" :: Data.Text.Text)))
                             (coe v5))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_182 v6)
                          (coe addInt (coe (1 :: Integer)) (coe v7)) (coe v8)
                          (coe MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154 (coe v9)))
                       (coe
                          C_failure_330
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("Lambda parameter '" :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   ("' used with quantity " :: Data.Text.Text)
                                   (coe
                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                      (MAlonzo.Code.Once.Type.d_showQuantity_30
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140
                                            (coe v9) (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                         (" but inferred lambdas default to " :: Data.Text.Text)
                                         (MAlonzo.Code.Once.Type.d_showQuantity_30
                                            (coe MAlonzo.Code.Once.Type.C_Many_10))))))))
                C_failure_330 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v2 v3 v4
        -> let v5 = d_inferElabImpl_1132 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_328 v6 v7 v8 v9 v10
                  -> let v11
                           = d_inferElabImpl_1132
                               (coe du_extendNamedCtx''_1666 (coe v0) (coe v2) (coe v6) (coe v9))
                               (coe v4) in
                     coe
                       (case coe v11 of
                          C_success_328 v12 v13 v14 v15 v16
                            -> coe
                                 C_success_328 (coe v12)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_let''_290 v6 v7 v13)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8)
                                    (coe addInt (coe (1 :: Integer)) (coe v14)))
                                 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154 (coe v16)))
                          C_failure_330 v12 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_330 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v2 v3
        -> let v4 = d_inferElabImpl_1132 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_328 v5 v6 v7 v8 v9
                  -> let v10
                           = d_inferElabImpl_1132
                               (coe du_bumpFresh''_1560 (coe v0) (coe v8)) (coe v3) in
                     coe
                       (case coe v10 of
                          C_success_328 v11 v12 v13 v14 v15
                            -> coe
                                 C_success_328
                                 (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v5) (coe v11))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_214 v6 v12)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v13))
                                 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v9)
                                    (coe v15))
                          C_failure_330 v11 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_330 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v2 v3 v4 v5 v6
        -> coe
             du_inferCase_1766 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe d_inferElabImpl_1132 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe
             C_success_328 (coe MAlonzo.Code.Once.Type.C_Unit_44)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_272)
             (coe (0 :: Integer)) (coe d_freshCounter_378 (coe v0))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_372 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v2
        -> coe
             C_success_328 (coe MAlonzo.Code.Once.Type.C_Int_60)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_int_296 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_378 (coe v0))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_372 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v2
        -> coe
             C_success_328 (coe MAlonzo.Code.Once.Type.C_Str_64)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_str_302 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_378 (coe v0))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_372 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v2 v3
        -> coe d_inferElabImpl_1132 (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v2 v3 v4
        -> coe
             du_inferOp_1878 (coe v0) (coe v2) (coe v4)
             (coe d_inferElabImpl_1132 (coe v0) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v3
        -> coe
             du_inferNeg_1926 (coe d_inferElabImpl_1132 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferApp
d_inferApp_1384 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_314 -> T_InferElabResult_314
d_inferApp_1384 v0 ~v1 v2 v3 = du_inferApp_1384 v0 v2 v3
du_inferApp_1384 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_314 -> T_InferElabResult_314
du_inferApp_1384 v0 v1 v2
  = case coe v2 of
      C_success_328 v3 v4 v5 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__48 v8 v9
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__50 v8 v9
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v8 v9 v10
               -> coe
                    du_inferArg_1418 (coe v8) (coe v9) (coe v10) (coe v4) (coe v5)
                    (coe v7)
                    (coe
                       d_inferElabImpl_1132 (coe du_bumpFreshTo_1406 (coe v0) (coe v6))
                       (coe v1))
             MAlonzo.Code.Once.Type.C_Eff_54 v8 v9
               -> coe
                    du_inferArgEff_1484 (coe v8) (coe v9) (coe v4) (coe v5) (coe v7)
                    (coe
                       d_inferElabImpl_1132 (coe du_bumpFreshToEff_1472 (coe v0) (coe v6))
                       (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v8
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v8
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_TVar_68 v8
               -> coe
                    C_failure_330
                    (coe ("Expected function type in application" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_330 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.bumpFreshTo
d_bumpFreshTo_1406 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_NamedCtx_360 -> Integer -> T_NamedCtx_360
d_bumpFreshTo_1406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_bumpFreshTo_1406 v10 v11
du_bumpFreshTo_1406 :: T_NamedCtx_360 -> Integer -> T_NamedCtx_360
du_bumpFreshTo_1406 v0 v1
  = case coe v0 of
      C_mkCtx_382 v2 v3 v4 v5 v6
        -> coe C_mkCtx_382 (coe v2) (coe v3) (coe v4) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferArg
d_inferArg_1418 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_314 -> T_InferElabResult_314
d_inferArg_1418 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 v9 v10
  = du_inferArg_1418 v3 v4 v5 v6 v7 v9 v10
du_inferArg_1418 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_314 -> T_InferElabResult_314
du_inferArg_1418 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_success_328 v7 v8 v9 v10 v11
        -> let v12 = d__'8799'T__40 (coe v0) (coe v7) in
           coe
             (case coe v12 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                  -> if coe v13
                       then coe
                              seq (coe v14)
                              (coe
                                 C_success_328 (coe v2)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_app_194 v7 v1 v3 v8)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v4) (coe v9))
                                 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v5)
                                    (coe v11)))
                       else coe
                              seq (coe v14)
                              (coe
                                 C_failure_330
                                 (coe ("Type mismatch in application" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_330 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.bumpFreshToEff
d_bumpFreshToEff_1472 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_NamedCtx_360 -> Integer -> T_NamedCtx_360
d_bumpFreshToEff_1472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_bumpFreshToEff_1472 v9 v10
du_bumpFreshToEff_1472 ::
  T_NamedCtx_360 -> Integer -> T_NamedCtx_360
du_bumpFreshToEff_1472 v0 v1
  = case coe v0 of
      C_mkCtx_382 v2 v3 v4 v5 v6
        -> coe C_mkCtx_382 (coe v2) (coe v3) (coe v4) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferArgEff
d_inferArgEff_1484 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_314 -> T_InferElabResult_314
d_inferArgEff_1484 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_inferArgEff_1484 v3 v4 v5 v6 v8 v9
du_inferArgEff_1484 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_314 -> T_InferElabResult_314
du_inferArgEff_1484 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_328 v6 v7 v8 v9 v10
        -> let v11 = d__'8799'T__40 (coe v0) (coe v6) in
           coe
             (case coe v11 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                  -> if coe v12
                       then coe
                              seq (coe v13)
                              (coe
                                 C_success_328 (coe v1)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_effApp_204 v6 v2 v7)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v8))
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v4)
                                    (coe v10)))
                       else coe
                              seq (coe v13)
                              (coe
                                 C_failure_330
                                 (coe ("Type mismatch in effect application" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_330 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.bumpFresh'
d_bumpFresh''_1560 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_360 -> Integer -> T_NamedCtx_360
d_bumpFresh''_1560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_bumpFresh''_1560 v8 v9
du_bumpFresh''_1560 :: T_NamedCtx_360 -> Integer -> T_NamedCtx_360
du_bumpFresh''_1560 v0 v1
  = case coe v0 of
      C_mkCtx_382 v2 v3 v4 v5 v6
        -> coe C_mkCtx_382 (coe v2) (coe v3) (coe v4) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.extendNamedCtx'
d_extendNamedCtx''_1666 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> Integer -> T_NamedCtx_360
d_extendNamedCtx''_1666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
                        v11 v12
  = du_extendNamedCtx''_1666 v9 v10 v11 v12
du_extendNamedCtx''_1666 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> Integer -> T_NamedCtx_360
du_extendNamedCtx''_1666 v0 v1 v2 v3
  = case coe v0 of
      C_mkCtx_382 v4 v5 v6 v7 v8
        -> coe
             C_mkCtx_382 (coe addInt (coe (1 :: Integer)) (coe v4))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v5)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v6) (coe v2))
             (coe v3) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.extendCtx'
d_extendCtx''_1750 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> Integer -> T_NamedCtx_360
d_extendCtx''_1750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_extendCtx''_1750 v6 v7 v8 v9
du_extendCtx''_1750 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> Integer -> T_NamedCtx_360
du_extendCtx''_1750 v0 v1 v2 v3
  = case coe v0 of
      C_mkCtx_382 v4 v5 v6 v7 v8
        -> coe
             C_mkCtx_382 (coe addInt (coe (1 :: Integer)) (coe v4))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v5)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v6) (coe v2))
             (coe v3) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferCase
d_inferCase_1766 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_314 -> T_InferElabResult_314
d_inferCase_1766 v0 ~v1 v2 v3 v4 v5 v6
  = du_inferCase_1766 v0 v2 v3 v4 v5 v6
du_inferCase_1766 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_314 -> T_InferElabResult_314
du_inferCase_1766 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_328 v6 v7 v8 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C_Unit_44
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_46
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__48 v11 v12
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__50 v11 v12
               -> coe
                    du_inferLeft_1786 (coe v0) (coe v3) (coe v4) (coe v11) (coe v12)
                    (coe v7) (coe v8) (coe v10)
                    (coe
                       d_inferElabImpl_1132
                       (coe du_extendCtx''_1750 (coe v0) (coe v1) (coe v11) (coe v9))
                       (coe v2))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v11 v12 v13
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Eff_54 v11 v12
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v11
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v11
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_60
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_62
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_64
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_66
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_TVar_68 v11
               -> coe
                    C_failure_330 (coe ("Expected sum type in case" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_330 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferLeft
d_inferLeft_1786 ::
  T_NamedCtx_360 ->
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
  T_InferElabResult_314 -> T_InferElabResult_314
d_inferLeft_1786 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 ~v10 v11 v12
  = du_inferLeft_1786 v0 v4 v5 v6 v7 v8 v9 v11 v12
du_inferLeft_1786 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_314 -> T_InferElabResult_314
du_inferLeft_1786 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_success_328 v9 v10 v11 v12 v13
        -> coe
             du_inferRight_1804 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
             (coe v9) (coe v10) (coe v11) (coe v13)
             (coe
                d_inferElabImpl_1132
                (coe du_extendCtx''_1750 (coe v0) (coe v1) (coe v4) (coe v12))
                (coe v2))
      C_failure_330 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._._.inferRight
d_inferRight_1804 ::
  T_NamedCtx_360 ->
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
  T_InferElabResult_314 -> T_InferElabResult_314
d_inferRight_1804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12
                  v13 v14 ~v15 v16 v17
  = du_inferRight_1804 v6 v7 v8 v9 v11 v12 v13 v14 v16 v17
du_inferRight_1804 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_314 -> T_InferElabResult_314
du_inferRight_1804 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_success_328 v10 v11 v12 v13 v14
        -> let v15 = d__'8799'T__40 (coe v5) (coe v10) in
           coe
             (case coe v15 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                  -> if coe v16
                       then coe
                              seq (coe v17)
                              (coe
                                 C_success_328 (coe v10)
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
                                 C_failure_330
                                 (coe ("Case branches have different types" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_330 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.bumpFresh'
d_bumpFresh''_1866 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_360 -> Integer -> T_NamedCtx_360
d_bumpFresh''_1866 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_bumpFresh''_1866 v4 v5
du_bumpFresh''_1866 :: T_NamedCtx_360 -> Integer -> T_NamedCtx_360
du_bumpFresh''_1866 v0 v1
  = case coe v0 of
      C_mkCtx_382 v2 v3 v4 v5 v6
        -> coe C_mkCtx_382 (coe v2) (coe v3) (coe v4) (coe v1) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferOp
d_inferOp_1878 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_314 -> T_InferElabResult_314
d_inferOp_1878 v0 v1 ~v2 v3 v4 = du_inferOp_1878 v0 v1 v3 v4
du_inferOp_1878 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_314 -> T_InferElabResult_314
du_inferOp_1878 v0 v1 v2 v3
  = case coe v3 of
      C_success_328 v4 v5 v6 v7 v8
        -> let v9
                 = coe
                     C_failure_330
                     (coe
                        ("Binary operator requires Int operands" :: Data.Text.Text)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Type.C_Int_60
                  -> coe
                       du_inferOp2_1894 (coe v1) (coe v5) (coe v6) (coe v8)
                       (coe
                          d_inferElabImpl_1132 (coe du_bumpFresh''_1866 (coe v0) (coe v7))
                          (coe v2))
                _ -> coe v9)
      C_failure_330 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferOp2
d_inferOp2_1894 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_314 -> T_InferElabResult_314
d_inferOp2_1894 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
  = du_inferOp2_1894 v1 v4 v5 v7 v8
du_inferOp2_1894 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_314 -> T_InferElabResult_314
du_inferOp2_1894 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_328 v5 v6 v7 v8 v9
        -> let v10
                 = coe
                     C_failure_330
                     (coe
                        ("Binary operator requires Int operands" :: Data.Text.Text)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Once.Type.C_Int_60
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe MAlonzo.Code.Once.TypeCheck.Raw.d_isArithmeticOp_90 (coe v0))
                       (coe
                          C_success_328 (coe v5) (coe du_mkArithOp_1910 v0 v1 v6)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v2) (coe v7))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v3)
                             (coe v9)))
                       (coe
                          C_success_328
                          (coe
                             MAlonzo.Code.Once.Type.C__'43'__50
                             (coe MAlonzo.Code.Once.Type.C_Unit_44)
                             (coe MAlonzo.Code.Once.Type.C_Unit_44))
                          (coe du_mkCmpOp_1912 v0 v1 v6)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v2) (coe v7))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v3)
                             (coe v9)))
                _ -> coe v10)
      C_failure_330 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._._.mkArithOp
d_mkArithOp_1910 ::
  T_NamedCtx_360 ->
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
d_mkArithOp_1910 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12
  = du_mkArithOp_1910 v12
du_mkArithOp_1910 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_mkArithOp_1910 v0
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
d_mkCmpOp_1912 ::
  T_NamedCtx_360 ->
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
d_mkCmpOp_1912 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               v12
  = du_mkCmpOp_1912 v12
du_mkCmpOp_1912 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
du_mkCmpOp_1912 v0
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
d_inferNeg_1926 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_314 -> T_InferElabResult_314
d_inferNeg_1926 ~v0 ~v1 v2 = du_inferNeg_1926 v2
du_inferNeg_1926 :: T_InferElabResult_314 -> T_InferElabResult_314
du_inferNeg_1926 v0
  = case coe v0 of
      C_success_328 v1 v2 v3 v4 v5
        -> let v6
                 = coe
                     C_failure_330
                     (coe ("Negation requires Int operand" :: Data.Text.Text)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Type.C_Int_60
                  -> coe
                       C_success_328 (coe v1)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_338 v2) (coe v3)
                       (coe v4) (coe v5)
                _ -> coe v6)
      C_failure_330 v1 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_1940 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_314
d_inferElab_1940 v0 v1
  = let v2 = d_inferElabImpl_1132 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_success_328 v3 v4 v5 v6 v7
           -> let v8
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v8 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                             (coe v5))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v5)
                              (coe (7 :: Integer)))) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                     -> if coe v9
                          then coe seq (coe v10) (coe v2)
                          else coe
                                 seq (coe v10)
                                 (coe
                                    C_failure_330
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
                                             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v5)
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
         C_failure_330 v3 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_2006 ::
  T_NamedCtx_360 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 -> T_CheckElabResult_338
d_checkElab_2006 v0 v1 v2
  = let v3 = d_checkElabImpl_1128 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         C_success_352 v4 v5 v6 v7
           -> let v8
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v8 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                             (coe v5))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v5)
                              (coe (7 :: Integer)))) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                     -> if coe v9
                          then coe seq (coe v10) (coe v3)
                          else coe
                                 seq (coe v10)
                                 (coe
                                    C_failure_354
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
                                             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v5)
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
         C_failure_354 v4 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExprTyped
d_compileExprTyped_2074 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_12
d_compileExprTyped_2074 v0 v1
  = let v2
          = d_checkElabImpl_1128 (coe d_emptyCtx_384) (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_success_352 v3 v4 v5 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v7 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                             (coe v4))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v4)
                              (coe (7 :: Integer)))) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                     -> if coe v8
                          then let v10 = seq (coe v9) (coe v2) in
                               coe
                                 (case coe v10 of
                                    C_success_352 v11 v12 v13 v14
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                              (coe (0 :: Integer))
                                              (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                              (coe v1) (coe v11))
                                    C_failure_354 v11
                                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          else (let v10
                                      = seq
                                          (coe v9)
                                          (coe
                                             C_failure_354
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
                                                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         ("\n" :: Data.Text.Text)
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            ("  Proven depth limit: 7\n"
                                                             ::
                                                             Data.Text.Text)
                                                            ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                             ::
                                                             Data.Text.Text))))))) in
                                coe
                                  (case coe v10 of
                                     C_success_352 v11 v12 v13 v14
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                               (coe v1) (coe v11))
                                     C_failure_354 v11
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_354 v3
           -> case coe v2 of
                C_success_352 v4 v5 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                          (coe (0 :: Integer))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v1)
                          (coe v4))
                C_failure_354 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExpr
d_compileExpr_2096 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_2096 v0
  = let v1 = d_inferElabImpl_1132 (coe d_emptyCtx_384) (coe v0) in
    coe
      (case coe v1 of
         C_success_328 v2 v3 v4 v5 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v7 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                             (coe v4))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v4)
                              (coe (7 :: Integer)))) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                     -> if coe v8
                          then let v10 = seq (coe v9) (coe v1) in
                               coe
                                 (case coe v10 of
                                    C_success_328 v11 v12 v13 v14 v15
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                                 (coe (0 :: Integer))
                                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                 (coe v11) (coe v12)))
                                    C_failure_330 v11
                                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          else (let v10
                                      = seq
                                          (coe v9)
                                          (coe
                                             C_failure_330
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
                                                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         ("\n" :: Data.Text.Text)
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            ("  Proven depth limit: 7\n"
                                                             ::
                                                             Data.Text.Text)
                                                            ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                             ::
                                                             Data.Text.Text))))))) in
                                coe
                                  (case coe v10 of
                                     C_success_328 v11 v12 v13 v14 v15
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                                  (coe (0 :: Integer))
                                                  (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                  (coe v11) (coe v12)))
                                     C_failure_330 v11
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_330 v2
           -> case coe v1 of
                C_success_328 v3 v4 v5 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                             (coe (0 :: Integer))
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v3)
                             (coe v4)))
                C_failure_330 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
