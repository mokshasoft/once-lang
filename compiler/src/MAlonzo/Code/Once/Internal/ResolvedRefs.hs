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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Internal.ResolvedRefs.GoodName
d_GoodName_6 :: MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> ()
d_GoodName_6 = erased
-- Once.Internal.ResolvedRefs.GoodRefs
d_GoodRefs_12 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> ()
d_GoodRefs_12 = erased
-- Once.Internal.ResolvedRefs.parts≢
d_parts'8802'_50 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_parts'8802'_50 = erased
-- Once.Internal.ResolvedRefs.one-name
d_one'45'name_58 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_one'45'name_58 ~v0 v1 = du_one'45'name_58 v1
du_one'45'name_58 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_one'45'name_58 v0
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
-- Once.Internal.ResolvedRefs.goodName?
d_goodName'63'_74 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_goodName'63'_74 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v1
        -> case coe v1 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe (\ v2 v3 -> coe du_'8869''45'elim'8242'_82)))
             (:) v2 v3
               -> case coe v3 of
                    []
                      -> coe
                           du_one'45'name_58
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v2)
                              (coe ("main" :: Data.Text.Text)))
                    (:) v4 v5
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                              (coe (\ v6 v7 -> coe du_'8869''45'elim'8242'_100)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.ResolvedRefs._.⊥-elim′
d_'8869''45'elim'8242'_82 ::
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim'8242'_82 ~v0 ~v1 = du_'8869''45'elim'8242'_82
du_'8869''45'elim'8242'_82 :: AgdaAny
du_'8869''45'elim'8242'_82 = MAlonzo.RTE.mazUnreachableError
-- Once.Internal.ResolvedRefs._.⊥-elim′
d_'8869''45'elim'8242'_100 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim'8242'_100 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8869''45'elim'8242'_100
du_'8869''45'elim'8242'_100 :: AgdaAny
du_'8869''45'elim'8242'_100 = MAlonzo.RTE.mazUnreachableError
-- Once.Internal.ResolvedRefs.goodRefs?
d_goodRefs'63'_106 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_goodRefs'63'_106 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v1
        -> coe d_goodName'63'_74 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_106 (coe v1)) (coe d_goodRefs'63'_106 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v1 v2
        -> coe d_goodRefs'63'_106 (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_106 (coe v2)) (coe d_goodRefs'63'_106 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_106 (coe v1)) (coe d_goodRefs'63'_106 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_106 (coe v1))
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                (coe d_goodRefs'63'_106 (coe v3))
                (coe d_goodRefs'63'_106 (coe v5)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v1 v2
        -> coe d_goodRefs'63'_106 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe d_goodRefs'63'_106 (coe v2)) (coe d_goodRefs'63'_106 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v1
        -> coe d_goodRefs'63'_106 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
