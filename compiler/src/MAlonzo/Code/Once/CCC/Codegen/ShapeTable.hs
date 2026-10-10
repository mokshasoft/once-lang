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

module MAlonzo.Code.Once.CCC.Codegen.ShapeTable where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Machine.ShapeAt
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Codegen.ShapeTable.RegExpect
d_RegExpect_8 = ()
data T_RegExpect_8
  = C_e'45'any_10 | C_e'45'repr_12 MAlonzo.Code.Once.IRTy.T_IRTy_6 |
    C_e'45'inl_14 MAlonzo.Code.Once.IRTy.T_IRTy_6
                  MAlonzo.Code.Once.IRTy.T_IRTy_6 |
    C_e'45'inr_16 MAlonzo.Code.Once.IRTy.T_IRTy_6
                  MAlonzo.Code.Once.IRTy.T_IRTy_6 |
    C_e'45'tag_18 Integer | C_e'45'word_20 |
    C_e'45'fresh_22 (Maybe T_RegExpect_8) (Maybe T_RegExpect_8)
-- Once.CCC.Codegen.ShapeTable.SlotEnv
d_SlotEnv_24 :: ()
d_SlotEnv_24 = erased
-- Once.CCC.Codegen.ShapeTable.Expect
d_Expect_26 = ()
data T_Expect_26
  = C_mkExpect_40 T_RegExpect_8 T_RegExpect_8
                  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.CCC.Codegen.ShapeTable.Expect.e-in1
d_e'45'in1_34 :: T_Expect_26 -> T_RegExpect_8
d_e'45'in1_34 v0
  = case coe v0 of
      C_mkExpect_40 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Expect.e-out
d_e'45'out_36 :: T_Expect_26 -> T_RegExpect_8
d_e'45'out_36 v0
  = case coe v0 of
      C_mkExpect_40 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Expect.e-slot
d_e'45'slot_38 ::
  T_Expect_26 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_e'45'slot_38 v0
  = case coe v0 of
      C_mkExpect_40 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.slot-get
d_slot'45'get_42 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_RegExpect_8
d_slot'45'get_42 v0 v1
  = case coe v0 of
      [] -> coe C_e'45'any_10
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                 (coe v4))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                               (coe eqInt (coe v4) (coe v1))) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe seq (coe v8) (coe v5)
                              else coe seq (coe v8) (coe d_slot'45'get_42 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.slot-put
d_slot'45'put_74 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  T_RegExpect_8 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_slot'45'put_74 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.CCC.Codegen.ShapeTable.LabelEnv
d_LabelEnv_82 :: ()
d_LabelEnv_82 = erased
-- Once.CCC.Codegen.ShapeTable.func-eq
d_func'45'eq_84 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> Bool
d_func'45'eq_84 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C_K_8 v3
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_K_8 v4
                  -> coe d_ty'45'eq_86 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_Id_10
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_Id_10
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'8853'__12 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'8853'__12 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_func'45'eq_84 (coe v3) (coe v5))
                       (coe d_func'45'eq_84 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'8855'__14 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'8855'__14 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_func'45'eq_84 (coe v3) (coe v5))
                       (coe d_func'45'eq_84 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.ShapeTable.ty-eq
d_ty'45'eq_86 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Bool
d_ty'45'eq_86 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C_Unit_16
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_Unit_16
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'42'__20 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_86 (coe v3) (coe v5))
                       (coe d_ty'45'eq_86 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'43'__22 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_86 (coe v3) (coe v5))
                       (coe d_ty'45'eq_86 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'8667'__24 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'8667'__24 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_86 (coe v3) (coe v5))
                       (coe d_ty'45'eq_86 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v4
                  -> coe d_func'45'eq_84 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v3
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v4
                  -> coe d_func'45'eq_84 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_Int_30
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_Int_30
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_Float_32
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_Float_32
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.nat-eq
d_nat'45'eq_140 :: Integer -> Integer -> Bool
d_nat'45'eq_140 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         0 -> case coe v1 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
              coe
                (case coe v1 of
                   _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                       let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                       coe (coe d_nat'45'eq_140 (coe v3) (coe v4))
                   _ -> coe v2))
-- Once.CCC.Codegen.ShapeTable.sub-reg
d_sub'45'reg_146 :: T_RegExpect_8 -> T_RegExpect_8 -> Bool
d_sub'45'reg_146 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v1 of
         C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_e'45'repr_12 v3
           -> case coe v0 of
                C_e'45'repr_12 v4 -> coe d_ty'45'eq_86 (coe v4) (coe v3)
                C_e'45'inl_14 v4 v5
                  -> coe
                       d_ty'45'eq_86
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v4) (coe v5)) (coe v3)
                C_e'45'inr_16 v4 v5
                  -> coe
                       d_ty'45'eq_86
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v4) (coe v5)) (coe v3)
                C_e'45'fresh_22 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                         -> case coe v6 of
                              C_e'45'repr_12 v7
                                -> case coe v5 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                       -> case coe v8 of
                                            C_e'45'repr_12 v9
                                              -> case coe v3 of
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
                                                     -> coe
                                                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                                          (coe d_ty'45'eq_86 (coe v7) (coe v10))
                                                          (coe d_ty'45'eq_86 (coe v9) (coe v11))
                                                   _ -> coe v2
                                            _ -> coe v2
                                     _ -> coe v2
                              C_e'45'tag_18 v7
                                -> case coe v7 of
                                     0 -> case coe v5 of
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                              -> case coe v8 of
                                                   C_e'45'repr_12 v9
                                                     -> case coe v3 of
                                                          MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
                                                            -> coe d_ty'45'eq_86 (coe v9) (coe v10)
                                                          _ -> coe v2
                                                   _ -> coe v2
                                            _ -> coe v2
                                     1 -> case coe v5 of
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                              -> case coe v8 of
                                                   C_e'45'repr_12 v9
                                                     -> case coe v3 of
                                                          MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
                                                            -> coe d_ty'45'eq_86 (coe v9) (coe v11)
                                                          _ -> coe v2
                                                   _ -> coe v2
                                            _ -> coe v2
                                     _ -> coe v2
                              _ -> coe v2
                       _ -> coe v2
                _ -> coe v2
         C_e'45'inl_14 v3 v4
           -> case coe v0 of
                C_e'45'inl_14 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_86 (coe v5) (coe v3))
                       (coe d_ty'45'eq_86 (coe v6) (coe v4))
                _ -> coe v2
         C_e'45'inr_16 v3 v4
           -> case coe v0 of
                C_e'45'inr_16 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_86 (coe v5) (coe v3))
                       (coe d_ty'45'eq_86 (coe v6) (coe v4))
                _ -> coe v2
         C_e'45'tag_18 v3
           -> case coe v0 of
                C_e'45'tag_18 v4 -> coe d_nat'45'eq_140 (coe v4) (coe v3)
                _ -> coe v2
         C_e'45'word_20
           -> case coe v0 of
                C_e'45'word_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.sub-slots
d_sub'45'slots_204 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Bool
d_sub'45'slots_204 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       d_sub'45'reg_146 (coe d_slot'45'get_42 (coe v0) (coe v4)) (coe v5))
                    (coe d_sub'45'slots_204 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.sub-expect
d_sub'45'expect_216 :: T_Expect_26 -> T_Expect_26 -> Bool
d_sub'45'expect_216 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         d_sub'45'reg_146 (coe d_e'45'in1_34 (coe v0))
         (coe d_e'45'in1_34 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe
            d_sub'45'reg_146 (coe d_e'45'out_36 (coe v0))
            (coe d_e'45'out_36 (coe v1)))
         (coe
            d_sub'45'slots_204 (coe d_e'45'slot_38 (coe v0))
            (coe d_e'45'slot_38 (coe v1))))
-- Once.CCC.Codegen.ShapeTable.as-sum-of
d_as'45'sum'45'of_222 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_as'45'sum'45'of_222 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.as-sum-of-inv
d_as'45'sum'45'of'45'inv_234 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_as'45'sum'45'of'45'inv_234 = erased
-- Once.CCC.Codegen.ShapeTable.as-sum
d_as'45'sum_240 ::
  T_RegExpect_8 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_as'45'sum_240 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_e'45'repr_12 v2
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v3 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
                  -> coe
                       d_as'45'sum'45'of_222
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v3) (coe v2))
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.is-ptr
d_is'45'ptr_250 :: T_RegExpect_8 -> Bool
d_is'45'ptr_250 v0
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_e'45'repr_12 v1
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_Unit_16
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.IRTy.C_Void_18
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v2
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.IRTy.C_Int_30
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.IRTy.C_Float_32
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'inl_14 v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_e'45'inr_16 v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_e'45'tag_18 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_e'45'word_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_e'45'fresh_22 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.fst-of
d_fst'45'of_276 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_RegExpect_8
d_fst'45'of_276 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
           -> coe C_e'45'repr_12 (coe v2)
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.load-fst
d_load'45'fst_282 :: T_RegExpect_8 -> T_RegExpect_8
d_load'45'fst_282 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         C_e'45'repr_12 v2
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v3 v4
                  -> coe C_e'45'repr_12 (coe v3)
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
                  -> coe
                       d_fst'45'of_276
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v3) (coe v2))
                _ -> coe v1
         C_e'45'fresh_22 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v4
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.snd-of
d_snd'45'of_292 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_RegExpect_8
d_snd'45'of_292 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
           -> coe C_e'45'repr_12 (coe v3)
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.load-snd
d_load'45'snd_298 :: T_RegExpect_8 -> T_RegExpect_8
d_load'45'snd_298 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         C_e'45'repr_12 v2
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v3 v4
                  -> coe C_e'45'repr_12 (coe v4)
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
                  -> coe
                       d_snd'45'of_292
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v3) (coe v2))
                _ -> coe v1
         C_e'45'inl_14 v2 v3 -> coe C_e'45'repr_12 (coe v2)
         C_e'45'inr_16 v2 v3 -> coe C_e'45'repr_12 (coe v3)
         C_e'45'fresh_22 v2 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v4
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.claim-at
d_claim'45'at_318 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 -> T_RegExpect_8
d_claim'45'at_318 ~v0 v1 v2 = du_claim'45'at_318 v1 v2
du_claim'45'at_318 ::
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 -> T_RegExpect_8
du_claim'45'at_318 v0 v1
  = let v2 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_Pure_130
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> case coe v3 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_202 -> coe C_e'45'word_20
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.sigop-claim
d_sigop'45'claim_324 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> T_RegExpect_8
d_sigop'45'claim_324 ~v0 v1 v2 = du_sigop'45'claim_324 v1 v2
du_sigop'45'claim_324 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> T_RegExpect_8
du_sigop'45'claim_324 v0 v1
  = coe
      du_claim'45'at_318
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_352 (coe v1))
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v0))
-- Once.CCC.Codegen.ShapeTable.step-expect
d_step'45'expect_330 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  T_Expect_26
d_step'45'expect_330 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in1_34 (coe v1)) (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254
        -> coe
             C_mkExpect_40 (coe d_e'45'out_36 (coe v1))
             (coe d_e'45'out_36 (coe v1)) (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1))
             (coe d_load'45'fst_282 (coe d_e'45'in1_34 (coe v1)))
             (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1))
             (coe d_load'45'snd_298 (coe d_e'45'in1_34 (coe v1)))
             (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260 v3
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1))
             (coe d_slot'45'get_42 (coe d_e'45'slot_38 (coe v1)) (coe v3))
             (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262 v3
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'out_36 (coe v1))
             (coe
                d_slot'45'put_74 (coe d_e'45'slot_38 (coe v1)) (coe v3)
                (coe d_e'45'out_36 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264
        -> let v3 = d_e'45'in1_34 (coe v1) in
           coe
             (case coe v3 of
                C_e'45'fresh_22 v4 v5
                  -> coe
                       C_mkExpect_40
                       (coe
                          C_e'45'fresh_22
                          (coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe d_e'45'out_36 (coe v1)))
                          (coe v5))
                       (coe d_e'45'out_36 (coe v1)) (coe d_e'45'slot_38 (coe v1))
                _ -> coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266
        -> let v3 = d_e'45'in1_34 (coe v1) in
           coe
             (case coe v3 of
                C_e'45'fresh_22 v4 v5
                  -> coe
                       C_mkExpect_40
                       (coe
                          C_e'45'fresh_22 (coe v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe d_e'45'out_36 (coe v1))))
                       (coe d_e'45'out_36 (coe v1)) (coe d_e'45'slot_38 (coe v1))
                _ -> coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2268 v3
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270 v3
        -> coe
             C_mkExpect_40
             (coe d_slot'45'get_42 (coe d_e'45'slot_38 (coe v1)) (coe v3))
             (coe d_e'45'out_36 (coe v1)) (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2272 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2274 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2276 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2278 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2280
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282
        -> coe
             C_mkExpect_40 (coe C_e'45'any_10) (coe C_e'45'any_10)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2284 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2286 v3
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'out_36 (coe v1))
             (coe
                d_slot'45'put_74 (coe d_e'45'slot_38 (coe v1)) (coe v3)
                (coe d_e'45'out_36 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288 v3
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1))
             (coe d_slot'45'get_42 (coe d_e'45'slot_38 (coe v1)) (coe v3))
             (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2290 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296 v3 v4 v5
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1))
             (coe du_sigop'45'claim_324 (coe v4) (coe v5))
             (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302 v3 v4 v5
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304 v3
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308 v3
        -> coe
             C_mkExpect_40 (coe d_e'45'in1_34 (coe v1))
             (coe C_e'45'tag_18 (coe v3)) (coe d_e'45'slot_38 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2310 v3 v4
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312 v3
        -> coe
             C_mkExpect_40
             (coe d_e'45'in1_34 (coe du_scrub'45'expect_526 (coe v1)))
             (coe
                C_e'45'fresh_22 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
             (coe d_e'45'slot_38 (coe du_scrub'45'expect_526 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2314 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_out'45'nz_382
               -> coe
                    C_mkExpect_40 (coe d_e'45'in1_34 (coe v1)) (coe C_e'45'any_10)
                    (coe d_e'45'slot_38 (coe v1))
             _ -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v4
               -> coe v0 v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v4
               -> coe
                    C_mkExpect_40 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v4
               -> coe v1
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v4
               -> let v5 = d_e'45'in1_34 (coe v1) in
                  coe
                    (let v6
                           = let v6 = d_as'45'sum_240 (coe v5) in
                             coe
                               (case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                    -> case coe v7 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                           -> coe
                                                C_mkExpect_40 (coe C_e'45'inr_16 (coe v8) (coe v9))
                                                (coe d_e'45'out_36 (coe v1))
                                                (coe d_e'45'slot_38 (coe v1))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                                  _ -> MAlonzo.RTE.mazUnreachableError) in
                     coe
                       (case coe v5 of
                          C_e'45'fresh_22 v7 v8 -> coe v1
                          _ -> coe v6))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v4 v5
               -> coe
                    C_mkExpect_40 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v4
               -> coe
                    C_mkExpect_40 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240 v4
               -> coe
                    C_mkExpect_40 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v4
               -> coe
                    C_mkExpect_40 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2320 v3
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable._.scrub
d_scrub_514 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 -> Integer -> T_RegExpect_8 -> T_RegExpect_8
d_scrub_514 ~v0 ~v1 ~v2 v3 = du_scrub_514 v3
du_scrub_514 :: T_RegExpect_8 -> T_RegExpect_8
du_scrub_514 v0
  = case coe v0 of
      C_e'45'fresh_22 v1 v2 -> coe C_e'45'any_10
      _ -> coe v0
-- Once.CCC.Codegen.ShapeTable._.scrub-slots
d_scrub'45'slots_518 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_scrub'45'slots_518 ~v0 ~v1 ~v2 v3 = du_scrub'45'slots_518 v3
du_scrub'45'slots_518 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_scrub'45'slots_518 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe du_scrub_514 (coe v4)))
                    (coe du_scrub'45'slots_518 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable._.scrub-expect
d_scrub'45'expect_526 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 -> Integer -> T_Expect_26 -> T_Expect_26
d_scrub'45'expect_526 ~v0 ~v1 ~v2 v3 = du_scrub'45'expect_526 v3
du_scrub'45'expect_526 :: T_Expect_26 -> T_Expect_26
du_scrub'45'expect_526 v0
  = coe
      C_mkExpect_40 (coe du_scrub_514 (coe d_e'45'in1_34 (coe v0)))
      (coe du_scrub_514 (coe d_e'45'out_36 (coe v0)))
      (coe du_scrub'45'slots_518 (coe d_e'45'slot_38 (coe v0)))
-- Once.CCC.Codegen.ShapeTable.is-word
d_is'45'word_650 :: T_RegExpect_8 -> Bool
d_is'45'word_650 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_e'45'word_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.is-fresh
d_is'45'fresh_652 :: T_RegExpect_8 -> Bool
d_is'45'fresh_652 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_e'45'fresh_22 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.is-just
d_is'45'just_656 :: () -> Maybe AgdaAny -> Bool
d_is'45'just_656 ~v0 v1 = du_is'45'just_656 v1
du_is'45'just_656 :: Maybe AgdaAny -> Bool
du_is'45'just_656 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.tag-site-ok
d_tag'45'site'45'ok_658 :: T_RegExpect_8 -> Bool
d_tag'45'site'45'ok_658 v0
  = let v1 = coe du_is'45'just_656 (coe d_as'45'sum_240 (coe v0)) in
    coe
      (case coe v0 of
         C_e'45'fresh_22 v2 v3
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (case coe v2 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v5 of
                          C_e'45'tag_18 v6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                          _ -> coe v4
                   _ -> coe v4)
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.not-any
d_not'45'any_666 :: T_RegExpect_8 -> Bool
d_not'45'any_666 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v0 of
         C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.site-ok
d_site'45'ok_668 ::
  T_Expect_26 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> Bool
d_site'45'ok_668 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256
           -> coe d_is'45'ptr_250 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258
           -> coe d_is'45'ptr_250 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260 v3
           -> coe
                d_not'45'any_666
                (coe d_slot'45'get_42 (coe d_e'45'slot_38 (coe v0)) (coe v3))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264
           -> coe d_is'45'fresh_652 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266
           -> coe d_is'45'fresh_652 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270 v3
           -> coe
                d_not'45'any_666
                (coe d_slot'45'get_42 (coe d_e'45'slot_38 (coe v0)) (coe v3))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288 v3
           -> coe
                d_not'45'any_666
                (coe d_slot'45'get_42 (coe d_e'45'slot_38 (coe v0)) (coe v3))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_out'45'nz_382
                  -> coe d_is'45'word_650 (coe d_e'45'out_36 (coe v0))
                _ -> coe v2
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v4
                  -> coe d_tag'45'site'45'ok_658 (coe d_e'45'in1_34 (coe v0))
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.ctrl-ok
d_ctrl'45'ok_698 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> Bool
d_ctrl'45'ok_698 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v4
           -> case coe v4 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v5
                  -> coe d_sub'45'expect_216 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v5
                  -> coe d_sub'45'expect_216 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v5
                  -> coe d_sub'45'expect_216 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v5
                  -> let v6 = d_e'45'in1_34 (coe v1) in
                     coe
                       (let v7
                              = let v7 = d_as'45'sum_240 (coe v6) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                       -> case coe v8 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                              -> coe
                                                   d_sub'45'expect_216
                                                   (coe
                                                      C_mkExpect_40
                                                      (coe C_e'45'inl_14 (coe v9) (coe v10))
                                                      (coe d_e'45'out_36 (coe v1))
                                                      (coe d_e'45'slot_38 (coe v1)))
                                                   (coe v0 v5)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                     _ -> MAlonzo.RTE.mazUnreachableError) in
                        coe
                          (case coe v6 of
                             C_e'45'fresh_22 v8 v9
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> case coe v10 of
                                           C_e'45'tag_18 v11
                                             -> case coe v11 of
                                                  0 -> coe d_sub'45'expect_216 (coe v1) (coe v0 v5)
                                                  _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                           _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                             _ -> coe v7))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v5 v6
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v3
         _ -> coe v3)
-- Once.CCC.Codegen.ShapeTable.check-shapes
d_check'45'shapes_806 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> Bool
d_check'45'shapes_806 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_site'45'ok_668 (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe d_ctrl'45'ok_698 (coe v0) (coe v1) (coe v3))
                (coe
                   d_check'45'shapes_806 (coe v0)
                   (coe d_step'45'expect_330 (coe v0) (coe v1) (coe v3)) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.scan-expect
d_scan'45'expect_820 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [T_Expect_26]
d_scan'45'expect_820 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe
                d_scan'45'expect_820 (coe v0)
                (coe d_step'45'expect_330 (coe v0) (coe v1) (coe v3)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.scan-length
d_scan'45'length_840 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scan'45'length_840 = erased
-- Once.CCC.Codegen.ShapeTable.post-expect
d_post'45'expect_858 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  T_Expect_26
d_post'45'expect_858 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4
        -> coe
             d_post'45'expect_858 (coe v0)
             (coe d_step'45'expect_330 (coe v0) (coe v1) (coe v3)) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.check-++
d_check'45''43''43'_880 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_check'45''43''43'_880 = erased
-- Once.CCC.Codegen.ShapeTable._.∧-assoc₂
d_'8743''45'assoc'8322'_910 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Bool ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc'8322'_910 = erased
-- Once.CCC.Codegen.ShapeTable.post-++
d_post'45''43''43'_938 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_post'45''43''43'_938 = erased
-- Once.CCC.Codegen.ShapeTable.IsHeap
d_IsHeap_956 :: MAlonzo.Code.Once.IR.T_AllocMode_4 -> ()
d_IsHeap_956 = erased
-- Once.CCC.Codegen.ShapeTable.HeapModed
d_HeapModed_962 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_HeapModed_962 = erased
-- Once.CCC.Codegen.ShapeTable.heap-moded
d_heap'45'moded_988 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
d_heap'45'moded_988 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_heap'45'moded_988 (coe v0) (coe v4) (coe v7))
             (coe d_heap'45'moded_988 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_heap'45'moded_988 (coe v0) (coe v8) (coe v6))
                    (coe d_heap'45'moded_988 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_heap'45'moded_988 (coe v8) (coe v1) (coe v6))
                    (coe d_heap'45'moded_988 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    d_heap'45'moded_988
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_In_94 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           d_heap'45'moded_988
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v1)))
                           (coe v1) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_Ana_122 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                      -> coe
                           d_heap'45'moded_988 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v9))
                           (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_126 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_SigOp_132 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_Call_138 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.entry-expect
d_entry'45'expect_1008 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_Expect_26
d_entry'45'expect_1008 v0
  = coe
      C_mkExpect_40 (coe C_e'45'repr_12 (coe v0)) (coe C_e'45'any_10)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Codegen.ShapeTable.at-pc
d_at'45'pc_1012 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_at'45'pc_1012 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_at'45'pc_1012 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.state-at
d_state'45'at_1026 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> T_Expect_26
d_state'45'at_1026 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe v1
      (:) v4 v5
        -> case coe v3 of
             0 -> coe v1
             _ -> let v6 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       d_state'45'at_1026 (coe v0)
                       (coe d_step'45'expect_330 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.∧-split
d_'8743''45'split_1056 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_1056 v0 v1 ~v2 = du_'8743''45'split_1056 v0 v1
du_'8743''45'split_1056 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_1056 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.CCC.Codegen.ShapeTable.check-at
d_check'45'at_1070 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'at_1070 v0 v1 v2 v3 ~v4 ~v5 ~v6
  = du_check'45'at_1070 v0 v1 v2 v3
du_check'45'at_1070 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_26) ->
  T_Expect_26 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'at_1070 v0 v1 v2 v3
  = case coe v2 of
      (:) v4 v5
        -> case coe v3 of
             0 -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_'8743''45'split_1056 (coe d_site'45'ok_668 (coe v1) (coe v4))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                             (coe d_ctrl'45'ok_698 (coe v0) (coe v1) (coe v4))
                             (coe
                                d_check'45'shapes_806 (coe v0)
                                (coe d_step'45'expect_330 (coe v0) (coe v1) (coe v4)) (coe v5)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_'8743''45'split_1056
                          (coe d_ctrl'45'ok_698 (coe v0) (coe v1) (coe v4))
                          (coe
                             d_check'45'shapes_806 (coe v0)
                             (coe d_step'45'expect_330 (coe v0) (coe v1) (coe v4)) (coe v5))))
             _ -> let v6 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_check'45'at_1070 (coe v0)
                       (coe d_step'45'expect_330 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.readLoc
d_readLoc_1110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1110 ~v0 = du_readLoc_1110
du_readLoc_1110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1110
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState
d_FlatState_1114 a0 = ()
-- Once.CCC.Codegen.ShapeTable.Sem._.fetch
d_fetch_1120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_fetch_1120 ~v0 = du_fetch_1120
du_fetch_1120 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
du_fetch_1120 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.falloc
d_falloc_1126 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_1126 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fclosure
d_fclosure_1128 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1128 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.flink
d_flink_1130 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1130 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.floc
d_floc_1132 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_floc_1132 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fpc
d_fpc_1134 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1134 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fret
d_fret_1136 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1136 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.CellShapeAt
d_CellShapeAt_1140 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.ShapeTable.Sem._.ShapeAt
d_ShapeAt_1142 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.ShapeTable.Sem._.TagAt
d_TagAt_1144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_TagAt_1144 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.BeforeFrontier
d_BeforeFrontier_1210 a0 a1 a2 = ()
-- Once.CCC.Codegen.ShapeTable.Sem.RegShape
d_RegShape_1226 a0 a1 a2 a3 a4 = ()
data T_RegShape_1226
  = C_rs'45'unit_1234 |
    C_rs'45'ptr_1242 MAlonzo.Code.Once.IR.T_AllocMode_4
                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 |
    C_rs'45'int_1246 | C_rs'45'float_1250
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt
d_InlAt_1262 a0 a1 a2 a3 a4 a5 = ()
data T_InlAt_1262
  = C_constructor_1310 MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
                       MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-m
d_i'45'm_1292 :: T_InlAt_1262 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_i'45'm_1292 v0
  = case coe v0 of
      C_constructor_1310 v1 v2 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-mA
d_i'45'mA_1294 ::
  T_InlAt_1262 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_i'45'mA_1294 v0
  = case coe v0 of
      C_constructor_1310 v1 v2 v3 v4 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-payload
d_i'45'payload_1296 ::
  T_InlAt_1262 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_i'45'payload_1296 v0
  = case coe v0 of
      C_constructor_1310 v1 v2 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-mode
d_i'45'mode_1298 :: T_InlAt_1262 -> AgdaAny
d_i'45'mode_1298 v0
  = case coe v0 of
      C_constructor_1310 v1 v2 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-tag
d_i'45'tag_1300 :: T_InlAt_1262 -> AgdaAny
d_i'45'tag_1300 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-cell
d_i'45'cell_1302 ::
  T_InlAt_1262 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'45'cell_1302 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-bf-p
d_i'45'bf'45'p_1304 ::
  T_InlAt_1262 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_i'45'bf'45'p_1304 v0
  = case coe v0 of
      C_constructor_1310 v1 v2 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-bf-s
d_i'45'bf'45's_1306 ::
  T_InlAt_1262 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_i'45'bf'45's_1306 v0
  = case coe v0 of
      C_constructor_1310 v1 v2 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-pay
d_i'45'pay_1308 ::
  T_InlAt_1262 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
d_i'45'pay_1308 v0
  = case coe v0 of
      C_constructor_1310 v1 v2 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt
d_InrAt_1322 a0 a1 a2 a3 a4 a5 = ()
data T_InrAt_1322
  = C_constructor_1370 MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
                       MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-m
d_r'45'm_1352 :: T_InrAt_1322 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_r'45'm_1352 v0
  = case coe v0 of
      C_constructor_1370 v1 v2 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-mB
d_r'45'mB_1354 ::
  T_InrAt_1322 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_r'45'mB_1354 v0
  = case coe v0 of
      C_constructor_1370 v1 v2 v3 v4 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-payload
d_r'45'payload_1356 ::
  T_InrAt_1322 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_r'45'payload_1356 v0
  = case coe v0 of
      C_constructor_1370 v1 v2 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-mode
d_r'45'mode_1358 :: T_InrAt_1322 -> AgdaAny
d_r'45'mode_1358 v0
  = case coe v0 of
      C_constructor_1370 v1 v2 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-tag
d_r'45'tag_1360 :: T_InrAt_1322 -> AgdaAny
d_r'45'tag_1360 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-cell
d_r'45'cell_1362 ::
  T_InrAt_1322 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r'45'cell_1362 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-bf-p
d_r'45'bf'45'p_1364 ::
  T_InrAt_1322 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_r'45'bf'45'p_1364 v0
  = case coe v0 of
      C_constructor_1370 v1 v2 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-bf-s
d_r'45'bf'45's_1366 ::
  T_InrAt_1322 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_r'45'bf'45's_1366 v0
  = case coe v0 of
      C_constructor_1370 v1 v2 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-pay
d_r'45'pay_1368 ::
  T_InrAt_1322 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
d_r'45'pay_1368 v0
  = case coe v0 of
      C_constructor_1370 v1 v2 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsR
d_MeetsR_1372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 -> ()
d_MeetsR_1372 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsCell
d_MeetsCell_1374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 -> ()
d_MeetsCell_1374 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MCell
d_MCell_1376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 -> ()
d_MCell_1376 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.FreshAt
d_FreshAt_1378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_RegExpect_8 ->
  Maybe T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 -> ()
d_FreshAt_1378 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsSlot
d_MeetsSlot_1538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 -> ()
d_MeetsSlot_1538 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.Meets
d_Meets_1638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Expect_26 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Meets_1638 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.func-eq-sound
d_func'45'eq'45'sound_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_func'45'eq'45'sound_1650 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.ty-eq-sound
d_ty'45'eq'45'sound_1656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ty'45'eq'45'sound_1656 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.nat-eq-sound
d_nat'45'eq'45'sound_1790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'eq'45'sound_1790 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.inl-shape
d_inl'45'shape_1816 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_InlAt_1262 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
d_inl'45'shape_1816 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_inl'45'shape_1816 v5
du_inl'45'shape_1816 ::
  T_InlAt_1262 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
du_inl'45'shape_1816 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_188
      (d_i'45'payload_1296 (coe v0)) (d_i'45'mA_1294 (coe v0))
      (d_i'45'mode_1298 (coe v0)) (d_i'45'bf'45'p_1304 (coe v0))
      (d_i'45'bf'45's_1306 (coe v0)) (d_i'45'pay_1308 (coe v0))
-- Once.CCC.Codegen.ShapeTable.Sem.inr-shape
d_inr'45'shape_1832 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_InrAt_1322 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
d_inr'45'shape_1832 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_inr'45'shape_1832 v5
du_inr'45'shape_1832 ::
  T_InrAt_1322 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
du_inr'45'shape_1832 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_206
      (d_r'45'payload_1356 (coe v0)) (d_r'45'mB_1354 (coe v0))
      (d_r'45'mode_1358 (coe v0)) (d_r'45'bf'45'p_1364 (coe v0))
      (d_r'45'bf'45's_1366 (coe v0)) (d_r'45'pay_1368 (coe v0))
-- Once.CCC.Codegen.ShapeTable.Sem.sub-reg-sound
d_sub'45'reg'45'sound_1846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_sub'45'reg'45'sound_1846 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_sub'45'reg'45'sound_1846 v1 v2 v7
du_sub'45'reg'45'sound_1846 ::
  T_RegExpect_8 -> T_RegExpect_8 -> AgdaAny -> AgdaAny
du_sub'45'reg'45'sound_1846 v0 v1 v2
  = case coe v1 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v3
        -> case coe v0 of
             C_e'45'repr_12 v4 -> coe v2
             C_e'45'inl_14 v4 v5
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> coe
                                  C_rs'45'ptr_1242 (d_i'45'm_1292 (coe v9))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_188
                                     (d_i'45'payload_1296 (coe v9)) (d_i'45'mA_1294 (coe v9))
                                     (d_i'45'mode_1298 (coe v9)) (d_i'45'bf'45'p_1304 (coe v9))
                                     (d_i'45'bf'45's_1306 (coe v9)) (d_i'45'pay_1308 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_e'45'inr_16 v4 v5
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> coe
                                  C_rs'45'ptr_1242 (d_r'45'm_1352 (coe v9))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_206
                                     (d_r'45'payload_1356 (coe v9)) (d_r'45'mB_1354 (coe v9))
                                     (d_r'45'mode_1358 (coe v9)) (d_r'45'bf'45'p_1364 (coe v9))
                                     (d_r'45'bf'45's_1366 (coe v9)) (d_r'45'pay_1368 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_e'45'fresh_22 v4 v5
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                      -> case coe v6 of
                           C_e'45'repr_12 v7
                             -> case coe v5 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v3)
                                            (case coe v2 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                      -> case coe v16 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                             -> case coe v17 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                    -> case coe
                                                                                              v20 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                           -> case coe
                                                                                                     v22 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                  -> case coe
                                                                                                            v24 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                         -> case coe
                                                                                                                   v18 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                -> case coe
                                                                                                                          v28 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                       -> case coe
                                                                                                                                 v30 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                              -> case coe
                                                                                                                                        v32 of
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                     -> coe
                                                                                                                                          C_rs'45'ptr_1242
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.IR.C_Heap_8)
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_148
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_606
                                                                                                                                                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                                                   (coe
                                                                                                                                                      addInt
                                                                                                                                                      (coe
                                                                                                                                                         (1 ::
                                                                                                                                                            Integer))
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                                                                                                                                            (coe
                                                                                                                                                               v9))))))
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_cell'45'shape'45'ptr_112
                                                                                                                                                v19
                                                                                                                                                v25
                                                                                                                                                v23
                                                                                                                                                v26)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_cell'45'shape'45'ptr_112
                                                                                                                                                v27
                                                                                                                                                v33
                                                                                                                                                v31
                                                                                                                                                v34))
                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           C_e'45'tag_18 v7
                             -> case coe v7 of
                                  0 -> case coe v5 of
                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                           -> coe
                                                seq (coe v8)
                                                (coe
                                                   seq (coe v3)
                                                   (case coe v2 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                        -> case coe v10 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                               -> case coe v12 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                      -> case coe v14 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                             -> case coe v16 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                    -> case coe
                                                                                              v18 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                           -> case coe
                                                                                                     v20 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                  -> case coe
                                                                                                            v22 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                         -> case coe
                                                                                                                   v24 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                -> coe
                                                                                                                     C_rs'45'ptr_1242
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.IR.C_Heap_8)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_188
                                                                                                                        v19
                                                                                                                        v25
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                        v23
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_606
                                                                                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                              (coe
                                                                                                                                 addInt
                                                                                                                                 (coe
                                                                                                                                    (1 ::
                                                                                                                                       Integer))
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                                                                                                                       (coe
                                                                                                                                          v9))))))
                                                                                                                        v26)
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> case coe v5 of
                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                           -> coe
                                                seq (coe v8)
                                                (coe
                                                   seq (coe v3)
                                                   (case coe v2 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                        -> case coe v10 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                               -> case coe v12 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                      -> case coe v14 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                             -> case coe v16 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                    -> case coe
                                                                                              v18 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                           -> case coe
                                                                                                     v20 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                  -> case coe
                                                                                                            v22 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                         -> case coe
                                                                                                                   v24 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                -> coe
                                                                                                                     C_rs'45'ptr_1242
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.IR.C_Heap_8)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_206
                                                                                                                        v19
                                                                                                                        v25
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                        v23
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_606
                                                                                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                              (coe
                                                                                                                                 addInt
                                                                                                                                 (coe
                                                                                                                                    (1 ::
                                                                                                                                       Integer))
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                                                                                                                       (coe
                                                                                                                                          v9))))))
                                                                                                                        v26)
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'inl_14 v3 v4 -> coe seq (coe v0) (coe v2)
      C_e'45'inr_16 v3 v4 -> coe seq (coe v0) (coe v2)
      C_e'45'tag_18 v3 -> erased
      C_e'45'word_20 -> coe seq (coe v0) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.slot-just
d_slot'45'just_2102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny -> AgdaAny
d_slot'45'just_2102 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_slot'45'just_2102 v1 v5
du_slot'45'just_2102 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_slot'45'just_2102 v0 v1
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v2 -> coe v1
      C_e'45'inl_14 v2 v3 -> coe v1
      C_e'45'inr_16 v2 v3 -> coe v1
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'word_20 -> coe v1
      C_e'45'fresh_22 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.just-slot
d_just'45'slot_2126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny -> AgdaAny
d_just'45'slot_2126 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_just'45'slot_2126 v1 v5
du_just'45'slot_2126 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_just'45'slot_2126 v0 v1
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v2 -> coe v1
      C_e'45'inl_14 v2 v3 -> coe v1
      C_e'45'inr_16 v2 v3 -> coe v1
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'word_20 -> coe v1
      C_e'45'fresh_22 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.sub-slot-sound
d_sub'45'slot'45'sound_2152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_sub'45'slot'45'sound_2152 ~v0 v1 v2 ~v3 v4 ~v5 ~v6 v7
  = du_sub'45'slot'45'sound_2152 v1 v2 v4 v7
du_sub'45'slot'45'sound_2152 ::
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_sub'45'slot'45'sound_2152 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_just'45'slot_2126 (coe v1)
             (coe
                du_sub'45'reg'45'sound_1846 (coe v0) (coe v1)
                (coe du_slot'45'just_2102 (coe v0) (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v1 of
             C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
             C_e'45'repr_12 v4
               -> coe
                    seq (coe v0) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             C_e'45'inl_14 v4 v5
               -> coe
                    seq (coe v0) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             C_e'45'inr_16 v4 v5
               -> coe
                    seq (coe v0) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             C_e'45'tag_18 v4
               -> coe
                    seq (coe v0) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             C_e'45'word_20
               -> coe
                    seq (coe v0) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             C_e'45'fresh_22 v4 v5
               -> coe
                    seq (coe v0) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.sub-slots-sound
d_sub'45'slots'45'sound_2332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'slots'45'sound_2332 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.sub-any
d_sub'45'any_2346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_RegExpect_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'any_2346 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.sub-expect-sound
d_sub'45'expect'45'sound_2394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Expect_26 ->
  T_Expect_26 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sub'45'expect'45'sound_2394 ~v0 v1 v2 v3 ~v4 v5
  = du_sub'45'expect'45'sound_2394 v1 v2 v3 v5
du_sub'45'expect'45'sound_2394 ::
  T_Expect_26 ->
  T_Expect_26 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sub'45'expect'45'sound_2394 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_sub'45'reg'45'sound_1846 (coe d_e'45'in1_34 (coe v0))
                       (coe d_e'45'in1_34 (coe v1)) (coe v4))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          du_sub'45'reg'45'sound_1846 (coe d_e'45'out_36 (coe v0))
                          (coe d_e'45'out_36 (coe v1)) (coe v6))
                       (coe
                          (\ v8 ->
                             coe
                               du_sub'45'slot'45'sound_2152
                               (coe d_slot'45'get_42 (coe d_e'45'slot_38 (coe v0)) (coe v8))
                               (coe d_slot'45'get_42 (coe d_e'45'slot_38 (coe v1)) (coe v8))
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_428
                                  (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v2))
                                  (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                                     (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
                                  v8)
                               (coe v7 v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.site-slot-written
d_site'45'slot'45'written_2416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_site'45'slot'45'written_2416 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.site-load-ptr
d_site'45'load'45'ptr_2444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'load'45'ptr_2444 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'load'45'ptr_2444 v1 v3 v6
du_site'45'load'45'ptr_2444 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'load'45'ptr_2444 v0 v1 v2
  = case coe v0 of
      C_e'45'repr_12 v3
        -> coe
             seq (coe v3)
             (coe
                seq (coe v2)
                (case coe v1 of
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v4
                     -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) erased
                   _ -> MAlonzo.RTE.mazUnreachableError))
      C_e'45'inl_14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'inr_16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'fresh_22 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 (coe v5))
                           (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.tag-of-shape
d_tag'45'of'45'shape_2526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'of'45'shape_2526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_tag'45'of'45'shape_2526 v7
du_tag'45'of'45'shape_2526 ::
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'of'45'shape_2526 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_188 v6 v8 v9 v12 v13 v14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             erased
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_206 v6 v8 v9 v12 v13 v14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl'45'reg_246 v7 v8 v10 v12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             erased
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr'45'reg_264 v7 v8 v10 v12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.tag-of-μ
d_tag'45'of'45'μ_2596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'of'45'μ_2596 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_tag'45'of'45'μ_2596 v5 v9
du_tag'45'of'45'μ_2596 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'of'45'μ_2596 v0 v1
  = coe seq (coe v0) (coe du_tag'45'of'45'shape_2526 (coe v1))
-- Once.CCC.Codegen.ShapeTable.Sem.site-branch-tag
d_site'45'branch'45'tag_2616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'branch'45'tag_2616 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'branch'45'tag_2616 v1 v3 v6
du_site'45'branch'45'tag_2616 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'branch'45'tag_2616 v0 v1 v2
  = case coe v0 of
      C_e'45'repr_12 v3
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v4 v5
               -> case coe v2 of
                    C_rs'45'ptr_1242 v7 v9
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                     (coe du_tag'45'of'45'shape_2526 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v4
               -> case coe v2 of
                    C_rs'45'ptr_1242 v6 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_278 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe
                                               du_go_2692
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                  (coe v4) (coe v3))
                                               (coe
                                                  d_as'45'sum'45'of_222
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                     (coe v4) (coe v3)))
                                               (coe v16)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'inl_14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'inr_16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'fresh_22 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
               -> case coe v5 of
                    C_e'45'tag_18 v6
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> case coe v10 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                           -> case coe v12 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                  -> case coe v14 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
                                                                 (coe v7))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v9)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v6) (coe v15)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.go
d_go_2692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17
  = du_go_2692 v9 v10 v17
du_go_2692 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2692 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe seq (coe v3) (coe du_tag'45'of'45'μ_2596 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.writeHeapMem-aux
d_writeHeapMem'45'aux_2738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem'45'aux_2738 ~v0 = du_writeHeapMem'45'aux_2738
du_writeHeapMem'45'aux_2738 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem'45'aux_2738 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_798 v2
      v3 v4
-- Once.CCC.Codegen.ShapeTable.Sem._.writeLocToHeap
d_writeLocToHeap_2740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_writeLocToHeap_2740 ~v0 = du_writeLocToHeap_2740
du_writeLocToHeap_2740 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
du_writeLocToHeap_2740
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_824
-- Once.CCC.Codegen.ShapeTable.Sem.nothing≢just
d_nothing'8802'just_2746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_2746 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.read-uw
d_read'45'uw_2758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'uw_2758 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.go
d_go_2794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_2794 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.tag-uw
d_tag'45'uw_2808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_tag'45'uw_2808 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.cell-uw
d_cell'45'uw_2850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_CellShapeAt_96 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_CellShapeAt_96
d_cell'45'uw_2850 v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8
  = du_cell'45'uw_2850 v0 v1 v2 v3 v5 v6 v8
du_cell'45'uw_2850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_CellShapeAt_96 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_CellShapeAt_96
du_cell'45'uw_2850 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_cell'45'shape'45'ptr_112 v9 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_cell'45'shape'45'ptr_112 v9
             v11 v13
             (coe
                du_shape'45'uw_2866 (coe v0) (coe v1) (coe v2) (coe v9) (coe v3)
                (coe v4) (coe v5) (coe v14))
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_cell'45'shape'45'inline_124 v10 v11
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_cell'45'shape'45'inline_124
             v10 v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.shape-uw
d_shape'45'uw_2866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
d_shape'45'uw_2866 v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_shape'45'uw_2866 v0 v2 v3 v4 v5 v6 v7 v9
du_shape'45'uw_2866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_98
du_shape'45'uw_2866 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'unit_134
        -> coe MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'unit_134
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_148 v14 v15 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v18 v19
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_148 v14 v15
                    (coe
                       du_cell'45'uw_2850 (coe v0) (coe v1) (coe v18) (coe v4) (coe v5)
                       (coe v6) (coe v16))
                    (coe
                       du_cell'45'uw_2850 (coe v0) (coe v1) (coe v19) (coe v4) (coe v5)
                       (coe v6) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure_170 v9 v14 v16 v17 v18 v21 v22 v23
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure_170 v9 v14
             v16 v17 v18 v21 v22
             (coe
                du_shape'45'uw_2866 (coe v0) (coe v1) (coe v9) (coe v14) (coe v4)
                (coe v5) (coe v6) (coe v23))
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_188 v13 v15 v16 v19 v20 v21
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v22 v23
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_188 v13 v15
                    v16 v19 v20
                    (coe
                       du_shape'45'uw_2866 (coe v0) (coe v1) (coe v22) (coe v13) (coe v4)
                       (coe v5) (coe v6) (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_206 v13 v15 v16 v19 v20 v21
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v22 v23
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_206 v13 v15
                    v16 v19 v20
                    (coe
                       du_shape'45'uw_2866 (coe v0) (coe v1) (coe v23) (coe v13) (coe v4)
                       (coe v5) (coe v6) (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure'45'reg_228 v9 v15 v16 v17 v18 v21
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure'45'reg_228
             v9 v15 v16 v17 v18 v21
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl'45'reg_246 v14 v15 v17 v19
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl'45'reg_246 v14
             v15 v17 v19
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr'45'reg_264 v14 v15 v17 v19
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr'45'reg_264 v14
             v15 v17 v19
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_278 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v15
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_278 v13
                    (coe
                       du_shape'45'uw_2866 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v15) (coe v2))
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'ν'45'susp_294 v10 v14 v15 v16 v18
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'ν'45'susp_294 v10
             v14 v15
             (coe
                du_cell'45'uw_2850 (coe v0) (coe v1) (coe v10) (coe v4) (coe v5)
                (coe v6) (coe v16))
             v18
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'int_306 v12 v13
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'int_306 v12 v13
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'float_318 v12 v13
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'float_318 v12 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.meets-cell-uw
d_meets'45'cell'45'uw_3126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_meets'45'cell'45'uw_3126 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_meets'45'cell'45'uw_3126 v0 v1 v2 v3 v4 v5 v8
du_meets'45'cell'45'uw_3126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_meets'45'cell'45'uw_3126 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> case coe v13 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v14)
                                                  (coe
                                                     du_shape'45'uw_2866 (coe v0) (coe v2) (coe v7)
                                                     (coe v8) (coe v3) (coe v4) (coe v5)
                                                     (coe v15)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'inl_14 v7 v8
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                        (coe
                                           du_inl'45'uw_3180 (coe v0) (coe v7) (coe v3) (coe v4)
                                           (coe v5) (coe v2) (coe v14))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'inr_16 v7 v8
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                        (coe
                                           du_inr'45'uw_3220 (coe v0) (coe v8) (coe v3) (coe v4)
                                           (coe v5) (coe v2) (coe v14))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'tag_18 v7 -> coe v6
      C_e'45'word_20 -> coe v6
      C_e'45'fresh_22 v7 v8
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.inl-uw
d_inl'45'uw_3180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  T_InlAt_1262 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  T_InlAt_1262 -> T_InlAt_1262
d_inl'45'uw_3180 v0 v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
                 ~v13 ~v14 v15 v16
  = du_inl'45'uw_3180 v0 v1 v4 v5 v6 v15 v16
du_inl'45'uw_3180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  T_InlAt_1262 -> T_InlAt_1262
du_inl'45'uw_3180 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_constructor_1310 v7 v8 v9 v10 v13 v14 v15
        -> coe
             C_constructor_1310 v7 v8 v9 v10 v13 v14
             (coe
                du_shape'45'uw_2866 (coe v0) (coe v5) (coe v1) (coe v9) (coe v2)
                (coe v3) (coe v4) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.inr-uw
d_inr'45'uw_3220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  T_InrAt_1322 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  T_InrAt_1322 -> T_InrAt_1322
d_inr'45'uw_3220 v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
                 ~v13 ~v14 v15 v16
  = du_inr'45'uw_3220 v0 v2 v4 v5 v6 v15 v16
du_inr'45'uw_3220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  T_InrAt_1322 -> T_InrAt_1322
du_inr'45'uw_3220 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_constructor_1370 v7 v8 v9 v10 v13 v14 v15
        -> coe
             C_constructor_1370 v7 v8 v9 v10 v13 v14
             (coe
                du_shape'45'uw_2866 (coe v0) (coe v5) (coe v1) (coe v9) (coe v2)
                (coe v3) (coe v4) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.fetch-at-pc
d_fetch'45'at'45'pc_3270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'pc_3270 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.fresh⇒ptr
d_fresh'8658'ptr_3286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fresh'8658'ptr_3286 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.site-store-ptr
d_site'45'store'45'ptr_3300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'store'45'ptr_3300 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'store'45'ptr_3300 v1 v3 v6
du_site'45'store'45'ptr_3300 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'store'45'ptr_3300 v0 v1 v2
  = coe du_site'45'load'45'ptr_2444 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.ShapeTable.Sem.site-out-word
d_site'45'out'45'word_3318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'out'45'word_3318 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_site'45'out'45'word_3318 v1 v6
du_site'45'out'45'word_3318 ::
  T_RegExpect_8 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'out'45'word_3318 v0 v1 = coe seq (coe v0) (coe v1)
