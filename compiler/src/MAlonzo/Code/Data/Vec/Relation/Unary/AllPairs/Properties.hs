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

module MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.All
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core

-- Data.Vec.Relation.Unary.AllPairs.Properties._.map⁺
d_map'8314'_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_map'8314'_50 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_map'8314'_50 v8 v9
du_map'8314'_50 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_map'8314'_50 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24
        -> coe v1
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8 v9
               -> coe
                    MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32
                    (coe
                       MAlonzo.Code.Data.Vec.Relation.Unary.All.Properties.du_map'8314'_54
                       (coe v9) (coe v5))
                    (coe du_map'8314'_50 (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Relation.Unary.AllPairs.Properties._.++⁺
d_'43''43''8314'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.All.T_All_50 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_'43''43''8314'_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 v10
  = du_'43''43''8314'_76 v6 v8 v9 v10
du_'43''43''8314'_76 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.All.T_All_50 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_'43''43''8314'_76 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24
        -> coe v2
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Data.Vec.Relation.Unary.All.C__'8759'__62 v15 v16
                      -> coe
                           MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32
                           (coe
                              MAlonzo.Code.Data.Vec.Relation.Unary.All.Properties.du_'43''43''8314'_78
                              (coe v11) (coe v7) (coe v15))
                           (coe du_'43''43''8314'_76 (coe v11) (coe v8) (coe v2) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Relation.Unary.AllPairs.Properties._.concat⁺
d_concat'8314'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.All.T_All_50 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_concat'8314'_112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_concat'8314'_112 v6 v7 v8
du_concat'8314'_112 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.All.T_All_50 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_concat'8314'_112 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Relation.Unary.All.C_'91''93'_56
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24)
      MAlonzo.Code.Data.Vec.Relation.Unary.All.C__'8759'__62 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v14 v15
                      -> coe
                           du_'43''43''8314'_76 (coe v9) (coe v6)
                           (coe du_concat'8314'_112 (coe v10) (coe v7) (coe v15))
                           (coe
                              MAlonzo.Code.Data.Vec.Relation.Unary.All.du_map_96
                              (coe
                                 (\ v16 ->
                                    coe
                                      MAlonzo.Code.Data.Vec.Relation.Unary.All.Properties.du_concat'8314'_186
                                      (coe v10)))
                              (coe v9)
                              (coe
                                 MAlonzo.Code.Data.Vec.Relation.Unary.All.Properties.du_All'45'swap_230
                                 (coe v10) (coe v9) (coe v14)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Relation.Unary.AllPairs.Properties._.take⁺
d_take'8314'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_take'8314'_138 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_take'8314'_138 v5 v6 v7
du_take'8314'_138 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_take'8314'_138 v0 v1 v2
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5 v6
                  -> case coe v2 of
                       MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v10 v11
                         -> coe
                              MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32
                              (coe
                                 MAlonzo.Code.Data.Vec.Relation.Unary.All.Properties.du_take'8314'_308
                                 (coe v3) (coe v6) (coe v10))
                              (coe du_take'8314'_138 (coe v3) (coe v6) (coe v11))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.Relation.Unary.AllPairs.Properties._.drop⁺
d_drop'8314'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_drop'8314'_158 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_drop'8314'_158 v5 v6 v7
du_drop'8314'_158 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_drop'8314'_158 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32 v7 v8
                  -> case coe v1 of
                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                         -> coe du_drop'8314'_158 (coe v3) (coe v11) (coe v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.Relation.Unary.AllPairs.Properties._.tabulate⁺
d_tabulate'8314'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   AgdaAny) ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_tabulate'8314'_184 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_tabulate'8314'_184 v4 v6
du_tabulate'8314'_184 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   AgdaAny) ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_tabulate'8314'_184 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C_'91''93'_24
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.C__'8759'__32
                (coe
                   MAlonzo.Code.Data.Vec.Relation.Unary.All.Properties.du_tabulate'8314'_264
                   (coe v2)
                   (coe
                      (\ v3 ->
                         coe
                           v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3) erased)))
                (coe
                   du_tabulate'8314'_184 (coe v2)
                   (coe
                      (\ v3 v4 v5 ->
                         coe
                           v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3)
                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v4)
                           (\ v6 -> coe v5 erased)))))
