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

module MAlonzo.Code.Once.Lang.ResolvedRefs where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Lang.ResolvedRefs._._∈?_
d__'8712''63'__8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712''63'__8
  = let v0 = MAlonzo.Code.Data.String.Properties.d__'8799'__54 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Once.Lang.ResolvedRefs.GoodName
d_GoodName_10 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> ()
d_GoodName_10 = erased
-- Once.Lang.ResolvedRefs.GoodRefs
d_GoodRefs_18 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 -> ()
d_GoodRefs_18 = erased
-- Once.Lang.ResolvedRefs.parts≢
d_parts'8802'_88 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_parts'8802'_88 = erased
-- Once.Lang.ResolvedRefs.one-name
d_one'45'name_98 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_one'45'name_98 ~v0 ~v1 v2 v3 = du_one'45'name_98 v2 v3
du_one'45'name_98 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_one'45'name_98 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v2)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           (coe
                                              (\ v6 v7 ->
                                                 coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   erased erased))))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ResolvedRefs.rigidFree-dec
d_rigidFree'45'dec_128 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_rigidFree'45'dec_128 v0
  = coe
      du_from_138
      (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v0))
-- Once.Lang.ResolvedRefs._.from
d_from_138 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_from_138 ~v0 v1 ~v2 = du_from_138 v1
du_from_138 ::
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_from_138 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ResolvedRefs._._.nothing≢just
d_nothing'8802'just_152 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_152 = erased
-- Once.Lang.ResolvedRefs.goodName?
d_goodName'63'_160 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_goodName'63'_160 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v2
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe (\ v3 v4 -> coe du_'8869''45'elim'8242'_170)))
             (:) v3 v4
               -> case coe v4 of
                    []
                      -> coe
                           du_one'45'name_98
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v3)
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
                              (coe
                                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                                 (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                              (coe v3) (coe v0))
                    (:) v5 v6
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                              (coe (\ v7 v8 -> coe du_'8869''45'elim'8242'_192)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ResolvedRefs._.⊥-elim′
d_'8869''45'elim'8242'_170 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim'8242'_170 ~v0 ~v1 ~v2
  = du_'8869''45'elim'8242'_170
du_'8869''45'elim'8242'_170 :: AgdaAny
du_'8869''45'elim'8242'_170 = MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ResolvedRefs._.⊥-elim′
d_'8869''45'elim'8242'_192 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim'8242'_192 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8869''45'elim'8242'_192
du_'8869''45'elim'8242'_192 :: AgdaAny
du_'8869''45'elim'8242'_192 = MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ResolvedRefs.goodRefs?
d_goodRefs'63'_200 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_goodRefs'63'_200 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Syntax.C_RQualified_38 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v2
        -> coe d_goodName'63'_160 (coe v0) (coe v2)
      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_200 (coe v0) (coe v2))
             (coe d_goodRefs'63'_200 (coe v0) (coe v3))
      MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v2 v3
        -> coe d_goodRefs'63'_200 (coe v0) (coe v3)
      MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v2 v3 v4
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_200 (coe v0) (coe v3))
             (coe d_goodRefs'63'_200 (coe v0) (coe v4))
      MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_200 (coe v0) (coe v2))
             (coe d_goodRefs'63'_200 (coe v0) (coe v3))
      MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v2 v3 v4 v5 v6
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_200 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                (coe d_goodRefs'63'_200 (coe v0) (coe v4))
                (coe d_goodRefs'63'_200 (coe v0) (coe v6)))
      MAlonzo.Code.Once.Lang.Syntax.C_RUnit_52
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_58 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_rigidFree'45'dec_128 (coe v3))
             (coe d_goodRefs'63'_200 (coe v0) (coe v2))
      MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v2 v3 v4
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_200 (coe v0) (coe v3))
             (coe d_goodRefs'63'_200 (coe v0) (coe v4))
      MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v3
        -> coe d_goodRefs'63'_200 (coe v0) (coe v3)
      MAlonzo.Code.Once.Lang.Syntax.C_RAna_64 v2 v3
        -> coe d_goodRefs'63'_200 (coe v0) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
