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

module MAlonzo.Code.Once.Internal.Laws.Order where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Laws.SubLaws
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Once.Internal.Laws.Order.⊑π-antisym
d_'8849'π'45'antisym_12 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849'π'45'antisym_12 = erased
-- Once.Internal.Laws.Order.purity-⊑-isPartialOrder
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
               MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_42 (coe v0)))
         (\ v0 v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Internal.Laws.SubLaws.du_'8849'π'45'trans_24 v3
              v4))
      erased
-- Once.Internal.Laws.Order.<:-antisym
d_'60''58''45'antisym_26 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'antisym_26 = erased
-- Once.Internal.Laws.Order.subtype-isPartialOrder
d_subtype'45'isPartialOrder_70 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_subtype'45'isPartialOrder_70 ~v0
  = du_subtype'45'isPartialOrder_70
du_subtype'45'isPartialOrder_70 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_subtype'45'isPartialOrder_70
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (coe
            (\ v0 v1 v2 ->
               coe
                 MAlonzo.Code.Once.Internal.Type.Sub.du_'60''58''45'refl_62
                 (coe v0)))
         (coe
            MAlonzo.Code.Once.Internal.Laws.SubLaws.du_'60''58''45'trans_90))
      erased
-- Once.Internal.Laws.Order.⊑ᵘ-antisym
d_'8849''7512''45'antisym_82 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849''7512''45'antisym_82 = erased
-- Once.Internal.Laws.Order.usage-⊑-isPartialOrder
d_usage'45''8849''45'isPartialOrder_94 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_usage'45''8849''45'isPartialOrder_94 ~v0
  = du_usage'45''8849''45'isPartialOrder_94
du_usage'45''8849''45'isPartialOrder_94 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_usage'45''8849''45'isPartialOrder_94
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (coe
            (\ v0 v1 v2 ->
               coe
                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'refl_138
                 (coe v0)))
         (coe
            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_218))
      erased
