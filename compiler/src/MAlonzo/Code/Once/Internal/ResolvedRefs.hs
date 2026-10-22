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

module MAlonzo.Code.Once.Internal.ResolvedRefs where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Internal.ResolvedRefs.GoodName
d_GoodName_6 :: MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> ()
d_GoodName_6 = erased
-- Once.Internal.ResolvedRefs.GoodRefs
d_GoodRefs_12 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 -> ()
d_GoodRefs_12 = erased
-- Once.Internal.ResolvedRefs.parts≢
d_parts'8802'_52 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_parts'8802'_52 = erased
-- Once.Internal.ResolvedRefs.one-name
d_one'45'name_60 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_one'45'name_60 ~v0 v1 = du_one'45'name_60 v1
du_one'45'name_60 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_one'45'name_60 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.ResolvedRefs.rigidFree-dec
d_rigidFree'45'dec_76 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_rigidFree'45'dec_76 v0
  = coe
      du_from_86
      (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_718 (coe v0))
-- Once.Internal.ResolvedRefs._.from
d_from_86 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_from_86 ~v0 v1 ~v2 = du_from_86 v1
du_from_86 ::
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_58 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_from_86 v0
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
-- Once.Internal.ResolvedRefs._._.nothing≢just
d_nothing'8802'just_100 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_100 = erased
-- Once.Internal.ResolvedRefs.goodName?
d_goodName'63'_106 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_goodName'63'_106 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v1
        -> case coe v1 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe (\ v2 v3 -> coe du_'8869''45'elim'8242'_114)))
             (:) v2 v3
               -> case coe v3 of
                    []
                      -> coe
                           du_one'45'name_60
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v2)
                              (coe ("main" :: Data.Text.Text)))
                    (:) v4 v5
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                              (coe (\ v6 v7 -> coe du_'8869''45'elim'8242'_132)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.ResolvedRefs._.⊥-elim′
d_'8869''45'elim'8242'_114 ::
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim'8242'_114 ~v0 ~v1 = du_'8869''45'elim'8242'_114
du_'8869''45'elim'8242'_114 :: AgdaAny
du_'8869''45'elim'8242'_114 = MAlonzo.RTE.mazUnreachableError
-- Once.Internal.ResolvedRefs._.⊥-elim′
d_'8869''45'elim'8242'_132 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim'8242'_132 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8869''45'elim'8242'_132
du_'8869''45'elim'8242'_132 :: AgdaAny
du_'8869''45'elim'8242'_132 = MAlonzo.RTE.mazUnreachableError
-- Once.Internal.ResolvedRefs.goodRefs?
d_goodRefs'63'_138 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_goodRefs'63'_138 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Syntax.C_RVar_36 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Internal.Syntax.C_RQualified_38 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v1
        -> coe d_goodName'63'_106 (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_138 (coe v1)) (coe d_goodRefs'63'_138 (coe v2))
      MAlonzo.Code.Once.Internal.Syntax.C_RLam_44 v1 v2
        -> coe d_goodRefs'63'_138 (coe v2)
      MAlonzo.Code.Once.Internal.Syntax.C_RLet_46 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_138 (coe v2)) (coe d_goodRefs'63'_138 (coe v3))
      MAlonzo.Code.Once.Internal.Syntax.C_RPair_48 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_138 (coe v1)) (coe d_goodRefs'63'_138 (coe v2))
      MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_138 (coe v1))
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                (coe d_goodRefs'63'_138 (coe v3))
                (coe d_goodRefs'63'_138 (coe v5)))
      MAlonzo.Code.Once.Internal.Syntax.C_RUnit_52
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Internal.Syntax.C_RAnnot_58 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_rigidFree'45'dec_76 (coe v2))
             (coe d_goodRefs'63'_138 (coe v1))
      MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_60 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_138 (coe v2)) (coe d_goodRefs'63'_138 (coe v3))
      MAlonzo.Code.Once.Internal.Syntax.C_RUnaryOp_62 v2
        -> coe d_goodRefs'63'_138 (coe v2)
      MAlonzo.Code.Once.Internal.Syntax.C_RAna_64 v1 v2
        -> coe d_goodRefs'63'_138 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
