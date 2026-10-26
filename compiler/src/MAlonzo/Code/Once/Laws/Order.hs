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

module MAlonzo.Code.Once.Laws.Order where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.Laws.Sub
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Once.Laws.Order.⊑π-antisym
d_'8849'π'45'antisym_10 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849'π'45'antisym_10 = erased
-- Once.Laws.Order.purity-⊑-isPartialOrder
d_purity'45''8849''45'isPartialOrder_12 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_purity'45''8849''45'isPartialOrder_12
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (coe
            (\ v0 v1 v2 ->
               MAlonzo.Code.Once.Type.Sub.d_'8849'π'45'refl_12 (coe v0)))
         (\ v0 v1 v2 v3 v4 ->
            coe MAlonzo.Code.Once.Laws.Sub.du_'8849'π'45'trans_22 v3 v4))
      erased
-- Once.Laws.Order.<:-antisym
d_'60''58''45'antisym_24 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''58''45'antisym_24 = erased
-- Once.Laws.Order.subtype-isPartialOrder
d_subtype'45'isPartialOrder_68 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_subtype'45'isPartialOrder_68 ~v0
  = du_subtype'45'isPartialOrder_68
du_subtype'45'isPartialOrder_68 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_subtype'45'isPartialOrder_68
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (coe
            (\ v0 v1 v2 ->
               coe MAlonzo.Code.Once.Type.Sub.du_'60''58''45'refl_32 (coe v0)))
         (coe MAlonzo.Code.Once.Laws.Sub.du_'60''58''45'trans_88))
      erased
-- Once.Laws.Order.⊑ᵘ-antisym
d_'8849''7512''45'antisym_80 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8849''7512''45'antisym_80 = erased
-- Once.Laws.Order.usage-⊑-isPartialOrder
d_usage'45''8849''45'isPartialOrder_92 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_usage'45''8849''45'isPartialOrder_92 ~v0
  = du_usage'45''8849''45'isPartialOrder_92
du_usage'45''8849''45'isPartialOrder_92 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_usage'45''8849''45'isPartialOrder_92
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (coe
            (\ v0 v1 v2 ->
               coe
                 MAlonzo.Code.Once.Context.du_'8849''7512''45'refl_100 (coe v0)))
         (coe MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180))
      erased
