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

module MAlonzo.Code.Once.Lang.Laws.Order where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Laws.SubLaws
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Once.Lang.Laws.Order.⊑π-antisym
d_'8849'π'45'antisym_12 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849'π'45'antisym_12 = erased
-- Once.Lang.Laws.Order.purity-⊑-isPartialOrder
d_purity'45''8849''45'isPartialOrder_14 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_purity'45''8849''45'isPartialOrder_14
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (coe
            (\ v0 v1 v2 ->
               MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v0)))
         (\ v0 v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Lang.Laws.SubLaws.du_'8849'π'45'trans_24 v3 v4))
      erased
-- Once.Lang.Laws.Order.<:-antisym
d_'60''58''45'antisym_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'antisym_24 = erased
-- Once.Lang.Laws.Order.subtype-isPartialOrder
d_subtype'45'isPartialOrder_66 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_subtype'45'isPartialOrder_66
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (coe
            (\ v0 v1 v2 ->
               MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v0)))
         (coe MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86))
      erased
-- Once.Lang.Laws.Order.⊑ᵘ-antisym
d_'8849''7512''45'antisym_78 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849''7512''45'antisym_78 = erased
-- Once.Lang.Laws.Order.usage-⊑-isPartialOrder
d_usage'45''8849''45'isPartialOrder_90 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_usage'45''8849''45'isPartialOrder_90 ~v0
  = du_usage'45''8849''45'isPartialOrder_90
du_usage'45''8849''45'isPartialOrder_90 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_usage'45''8849''45'isPartialOrder_90
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (coe
            (\ v0 v1 v2 ->
               coe
                 MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'refl_198
                 (coe v0)))
         (coe MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278))
      erased
