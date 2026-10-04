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

module MAlonzo.Code.Data.List.Relation.Binary.Subset.DecSetoid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.List.Relation.Binary.Subset.DecSetoid._._⊆_
d__'8838'__32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8838'__32 = erased
-- Data.List.Relation.Binary.Subset.DecSetoid._._⊇_
d__'8839'__34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8839'__34 = erased
-- Data.List.Relation.Binary.Subset.DecSetoid._._⊈_
d__'8840'__36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8840'__36 = erased
-- Data.List.Relation.Binary.Subset.DecSetoid._._⊉_
d__'8841'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8841'__38 = erased
-- Data.List.Relation.Binary.Subset.DecSetoid._⊆?_
d__'8838''63'__40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8838''63'__40 ~v0 ~v1 v2 v3 v4 = du__'8838''63'__40 v2 v3 v4
du__'8838''63'__40 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8838''63'__40 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      (:) v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d__'8799'__56
                        (MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_106
                           (coe v0))
                        v3)
                     (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then case coe v7 of
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                -> let v9 = coe du__'8838''63'__40 (coe v0) (coe v4) (coe v2) in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                          -> if coe v10
                                               then case coe v11 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                        -> coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v10)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                (coe
                                                                   du_'46'extendedlambda0_96
                                                                   (coe v0) (coe v2) (coe v12)
                                                                   (coe v3) (coe v8)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v11)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v10)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       else coe
                              seq (coe v7)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                 (coe v6)
                                 (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Subset.DecSetoid..extendedlambda0
d_'46'extendedlambda0_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'46'extendedlambda0_96 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_'46'extendedlambda0_96 v2 v3 v5 v6 v7 v8 v9
du_'46'extendedlambda0_96 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'46'extendedlambda0_96 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v9
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.Any.du_map_76
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_106
                           (coe v0)))
                     v5 v3 v10 v9))
             (coe v1) (coe v4)
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v9
        -> coe v2 v5 v9
      _ -> MAlonzo.RTE.mazUnreachableError
