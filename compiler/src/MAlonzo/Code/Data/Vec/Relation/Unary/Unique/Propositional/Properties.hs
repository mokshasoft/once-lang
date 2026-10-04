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

module MAlonzo.Code.Data.Vec.Relation.Unary.Unique.Propositional.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.Unique.Setoid.Properties

-- Data.Vec.Relation.Unary.Unique.Propositional.Properties._.map⁺
d_map'8314'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_map'8314'_44 ~v0 ~v1 ~v2 ~v3 ~v4 = du_map'8314'_44
du_map'8314'_44 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_map'8314'_44 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Vec.Relation.Unary.Unique.Setoid.Properties.du_map'8314'_104
      v2 v3
-- Data.Vec.Relation.Unary.Unique.Propositional.Properties._.drop⁺
d_drop'8314'_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_drop'8314'_60 ~v0 ~v1 ~v2 = du_drop'8314'_60
du_drop'8314'_60 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_drop'8314'_60
  = coe
      MAlonzo.Code.Data.Vec.Relation.Unary.Unique.Setoid.Properties.du_drop'8314'_126
-- Data.Vec.Relation.Unary.Unique.Propositional.Properties._.take⁺
d_take'8314'_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_take'8314'_68 ~v0 ~v1 ~v2 = du_take'8314'_68
du_take'8314'_68 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_take'8314'_68
  = coe
      MAlonzo.Code.Data.Vec.Relation.Unary.Unique.Setoid.Properties.du_take'8314'_134
-- Data.Vec.Relation.Unary.Unique.Propositional.Properties._.tabulate⁺
d_tabulate'8314'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_tabulate'8314'_86 ~v0 ~v1 v2 ~v3 = du_tabulate'8314'_86 v2
du_tabulate'8314'_86 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
du_tabulate'8314'_86 v0
  = coe
      MAlonzo.Code.Data.Vec.Relation.Unary.Unique.Setoid.Properties.du_tabulate'8314'_178
      (coe v0)
-- Data.Vec.Relation.Unary.Unique.Propositional.Properties._.lookup-injective
d_lookup'45'injective_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'injective_104 = erased
