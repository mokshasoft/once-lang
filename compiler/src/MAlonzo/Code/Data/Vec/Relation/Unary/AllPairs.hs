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

module MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.All
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Vec.Relation.Unary.AllPairs.head
d_head_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.All.T_All_50
d_head_22 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_head_22 v6
du_head_22 ::
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.All.T_All_50
du_head_22 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v4 v5
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Relation.Unary.AllPairs.tail
d_tail_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_tail_32 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_tail_32 v6
du_tail_32 ::
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_tail_32 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v4 v5
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Relation.Unary.AllPairs.uncons
d_uncons_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_uncons_42 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_uncons_42
du_uncons_42 ::
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_uncons_42
  = coe
      MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
      (coe du_head_22) (coe du_tail_32)
-- Data.Vec.Relation.Unary.AllPairs._.map
d_map_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_map_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 = du_map_54 v7 v8 v9
du_map_54 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_map_54 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24
        -> coe v2
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
               -> coe
                    MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32
                    (coe
                       MAlonzo.Code.Data.Vec.Relation.Unary.All.du_map_96 (coe v0 v9)
                       (coe v10) (coe v6))
                    (coe du_map_54 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Relation.Unary.AllPairs._.zipWith
d_zipWith_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_zipWith_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_zipWith_78 v9 v10 v11
du_zipWith_78 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_zipWith_78 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24
               -> coe seq (coe v4) (coe v3)
             MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
                      -> case coe v4 of
                           MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v16 v17
                             -> coe
                                  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32
                                  (coe
                                     MAlonzo.Code.Data.Vec.Relation.Unary.All.du_map_96 (coe v0 v11)
                                     (coe v12)
                                     (coe
                                        MAlonzo.Code.Data.Vec.Relation.Unary.All.du_zip_106
                                        (coe v12)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe v16))))
                                  (coe
                                     du_zipWith_78 (coe v0) (coe v12)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                        (coe v17)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Relation.Unary.AllPairs._.unzipWith
d_unzipWith_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzipWith_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_unzipWith_94 v9 v10 v11
du_unzipWith_94 ::
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzipWith_94 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v2)
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
               -> coe
                    MAlonzo.Code.Data.Product.Base.du_zip_198
                    (coe
                       MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32)
                    (coe
                       (\ v11 v12 ->
                          coe
                            MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32))
                    (coe
                       MAlonzo.Code.Data.Vec.Relation.Unary.All.du_unzip_116 (coe v10)
                       (coe
                          MAlonzo.Code.Data.Vec.Relation.Unary.All.du_map_96 (coe v0 v9)
                          (coe v10) (coe v6)))
                    (coe du_unzipWith_94 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Relation.Unary.AllPairs._.zip
d_zip_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_zip_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_zip_114 v7
du_zip_114 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_zip_114 v0 = coe du_zipWith_78 (coe (\ v1 v2 v3 -> v3)) (coe v0)
-- Data.Vec.Relation.Unary.AllPairs._.unzip
d_unzip_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzip_118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_unzip_118 v7
du_unzip_118 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzip_118 v0
  = coe du_unzipWith_94 (coe (\ v1 v2 v3 -> v3)) (coe v0)
-- Data.Vec.Relation.Unary.AllPairs.allPairs?
d_allPairs'63'_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_allPairs'63'_122 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_allPairs'63'_122 v5 v6
du_allPairs'63'_122 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_allPairs'63'_122 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe
                   MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24))
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
             (coe
                MAlonzo.Code.Data.Product.Base.du_uncurry_244
                (coe
                   MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32))
             (coe du_uncons_42)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                (coe
                   MAlonzo.Code.Data.Vec.Relation.Unary.All.du_all'63'_280 (coe v0 v3)
                   (coe v4))
                (coe du_allPairs'63'_122 (coe v0) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Relation.Unary.AllPairs.irrelevant
d_irrelevant_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irrelevant_134 = erased
-- Data.Vec.Relation.Unary.AllPairs.satisfiable
d_satisfiable_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_148 ~v0 ~v1 ~v2 ~v3 = du_satisfiable_148
du_satisfiable_148 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_148
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)
      (coe
         MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24)
