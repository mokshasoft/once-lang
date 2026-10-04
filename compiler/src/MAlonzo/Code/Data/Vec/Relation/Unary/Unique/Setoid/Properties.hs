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

module MAlonzo.Code.Data.Vec.Relation.Unary.Unique.Setoid.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Properties
import qualified MAlonzo.Code.Relation.Binary.Bundles

-- Data.Vec.Relation.Unary.Unique.Setoid.Properties._._._≈_
d__'8776'__48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__48 = erased
-- Data.Vec.Relation.Unary.Unique.Setoid.Properties._.map⁺
d_map'8314'_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_map'8314'_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_map'8314'_104 v9 v10
du_map'8314'_104 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_map'8314'_104 v0 v1
  = coe
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Properties.du_map'8314'_50
      (coe v0)
      (coe
         MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.du_map_54 erased
         (coe v0) (coe v1))
-- Data.Vec.Relation.Unary.Unique.Setoid.Properties._.drop⁺
d_drop'8314'_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_drop'8314'_126 ~v0 ~v1 ~v2 ~v3 = du_drop'8314'_126
du_drop'8314'_126 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_drop'8314'_126
  = coe
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Properties.du_drop'8314'_158
-- Data.Vec.Relation.Unary.Unique.Setoid.Properties._.take⁺
d_take'8314'_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_take'8314'_134 ~v0 ~v1 ~v2 ~v3 = du_take'8314'_134
du_take'8314'_134 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_take'8314'_134
  = coe
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Properties.du_take'8314'_138
-- Data.Vec.Relation.Unary.Unique.Setoid.Properties._.tabulate⁺
d_tabulate'8314'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_tabulate'8314'_178 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_tabulate'8314'_178 v3 v5
du_tabulate'8314'_178 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_tabulate'8314'_178 v0 v1
  = coe
      MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Properties.du_tabulate'8314'_184
      (coe v0) (coe (\ v2 v3 v4 v5 -> coe v4 (coe v1 v2 v3 v5)))
-- Data.Vec.Relation.Unary.Unique.Setoid.Properties._.lookup-injective
d_lookup'45'injective_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'injective_226 = erased
