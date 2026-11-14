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

module MAlonzo.Code.Once.TypeCheck.NumTable where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Spec.Float.Value
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.NumTable.NumView
d_NumView_8 a0 a1 = ()
data T_NumView_8
  = C_is'45'num_14 MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 |
    C_not'45'num_18
-- Once.TypeCheck.NumTable.numView
d_numView_24 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_NumView_8
d_numView_24 ~v0 v1 = du_numView_24 v1
du_numView_24 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_NumView_8
du_numView_24 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1 -> coe C_not'45'num_18
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_not'45'num_18
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_not'45'num_18
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe C_not'45'num_18
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe C_not'45'num_18
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe C_not'45'num_18
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1 -> coe C_not'45'num_18
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2 -> coe C_not'45'num_18
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe C_is'45'num_14 (coe MAlonzo.Code.Once.Spec.Theory.C_int_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             C_is'45'num_14 (coe MAlonzo.Code.Once.Spec.Theory.C_float_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.NumTable.⌜⌝ⁿ-inj
d_'8988''8989''8319''45'inj_32 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8988''8989''8319''45'inj_32 = erased
-- Once.TypeCheck.NumTable._≟ⁿ_
d__'8799''8319'__38 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''8319'__38 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Theory.C_int_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_int_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Spec.Theory.C_float_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Theory.C_float_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_int_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Theory.C_float_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.NumTable.has?
d_has'63'_44 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Theory_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_has'63'_44 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Theory.C_int_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_Neg_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Spec.Theory.C_int'45'neg_106))
             MAlonzo.Code.Once.Spec.Theory.C_Ring_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Spec.Theory.C_int'45'ring_108))
             MAlonzo.Code.Once.Spec.Theory.C_Division_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Spec.Theory.C_int'45'division_110))
             MAlonzo.Code.Once.Spec.Theory.C_Order_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Spec.Theory.C_int'45'order_112))
             MAlonzo.Code.Once.Spec.Theory.C_Equality_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Spec.Theory.C_int'45'equality_114))
             MAlonzo.Code.Once.Spec.Theory.C_Rounded_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Theory.C_float_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_Neg_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Spec.Theory.C_float'45'neg_116))
             MAlonzo.Code.Once.Spec.Theory.C_Ring_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Theory.C_Division_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Theory.C_Order_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Spec.Theory.C_float'45'order_120))
             MAlonzo.Code.Once.Spec.Theory.C_Equality_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Spec.Theory.C_float'45'equality_122))
             MAlonzo.Code.Once.Spec.Theory.C_Rounded_28
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Spec.Theory.C_float'45'rounded_118))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.NumTable.has-unique
d_has'45'unique_54 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Theory_16 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_has'45'unique_54 = erased
-- Once.TypeCheck.NumTable.Binary
d_Binary_56 :: MAlonzo.Code.Once.Spec.Theory.T_Shape_30 -> ()
d_Binary_56 = erased
-- Once.TypeCheck.NumTable.binary?
d_binary'63'_60 ::
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 -> AgdaAny
d_binary'63'_60 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Operator.C_plain_38 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32 v2
               -> coe seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Spec.Surface.Operator.C_o'37'_34
               -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Operator.C_dotted_40 v1
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.NumTable.pairDom
d_pairDom_68 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pairDom_68 = erased
-- Once.TypeCheck.NumTable.binDom
d_binDom_80 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_binDom_80 = erased
-- Once.TypeCheck.NumTable.negZero?
d_negZero'63'_92 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_negZero'63'_92 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Float.Value.C_pos_10
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      MAlonzo.Code.Once.Spec.Float.Value.C_neg_12
        -> case coe v1 of
             0 -> case coe v2 of
                    0 -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
                    _ -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.NumTable.numView-num
d_numView'45'num_98 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_numView'45'num_98 = erased
-- Once.TypeCheck.NumTable.≟ⁿ-refl
d_'8799''8319''45'refl_102 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8799''8319''45'refl_102 = erased
-- Once.TypeCheck.NumTable.has?-yes
d_has'63''45'yes_110 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Theory_16 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_has'63''45'yes_110 = erased
-- Once.TypeCheck.NumTable.negZero?-no
d_negZero'63''45'no_122 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Spec.Surface.Syntax.T_NegativeZero_88 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_negZero'63''45'no_122 v0 v1 v2 ~v3
  = du_negZero'63''45'no_122 v0 v1 v2
du_negZero'63''45'no_122 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_negZero'63''45'no_122 v0 v1 v2
  = let v3 = d_negZero'63'_92 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                else coe
                       seq (coe v5)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
         _ -> MAlonzo.RTE.mazUnreachableError)
