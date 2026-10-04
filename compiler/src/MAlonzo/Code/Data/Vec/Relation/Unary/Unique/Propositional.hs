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

module MAlonzo.Code.Data.Vec.Relation.Unary.Unique.Propositional where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.All
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core

-- Data.Vec.Relation.Unary.Unique.Propositional._.AllPairs
d_AllPairs_20 a0 a1 a2 a3 = ()
-- Data.Vec.Relation.Unary.Unique.Propositional._.head
d_head_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.All.T_All_50
d_head_24 ~v0 ~v1 = du_head_24
du_head_24 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.All.T_All_50
du_head_24 v0 v1 v2
  = coe MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.du_head_22 v2
-- Data.Vec.Relation.Unary.Unique.Propositional._.tail
d_tail_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_tail_26 ~v0 ~v1 = du_tail_26
du_tail_26 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_tail_26 v0 v1 v2
  = coe MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.du_tail_32 v2
