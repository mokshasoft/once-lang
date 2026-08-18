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
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Codegen.ShapeTable.RegExpect
d_RegExpect_8 = ()
data T_RegExpect_8
  = C_e'45'any_10 | C_e'45'repr_12 MAlonzo.Code.Once.IRTy.T_IRTy_6 |
    C_e'45'inl_14 MAlonzo.Code.Once.IRTy.T_IRTy_6
                  MAlonzo.Code.Once.IRTy.T_IRTy_6 |
    C_e'45'inr_16 MAlonzo.Code.Once.IRTy.T_IRTy_6
                  MAlonzo.Code.Once.IRTy.T_IRTy_6 |
    C_e'45'tag_18 Integer |
    C_e'45'fresh_20 (Maybe T_RegExpect_8) (Maybe T_RegExpect_8)
-- Once.CCC.Codegen.ShapeTable.SlotEnv
d_SlotEnv_22 :: ()
d_SlotEnv_22 = erased
-- Once.CCC.Codegen.ShapeTable.Expect
d_Expect_24 = ()
data T_Expect_24
  = C_mkExpect_38 T_RegExpect_8 T_RegExpect_8
                  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.CCC.Codegen.ShapeTable.Expect.e-in1
d_e'45'in1_32 :: T_Expect_24 -> T_RegExpect_8
d_e'45'in1_32 v0
  = case coe v0 of
      C_mkExpect_38 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Expect.e-out
d_e'45'out_34 :: T_Expect_24 -> T_RegExpect_8
d_e'45'out_34 v0
  = case coe v0 of
      C_mkExpect_38 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Expect.e-slot
d_e'45'slot_36 ::
  T_Expect_24 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_e'45'slot_36 v0
  = case coe v0 of
      C_mkExpect_38 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.slot-get
d_slot'45'get_40 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_RegExpect_8
d_slot'45'get_40 v0 v1
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
                              else coe seq (coe v8) (coe d_slot'45'get_40 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.slot-put
d_slot'45'put_72 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  T_RegExpect_8 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_slot'45'put_72 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.CCC.Codegen.ShapeTable.LabelEnv
d_LabelEnv_80 :: ()
d_LabelEnv_80 = erased
-- Once.CCC.Codegen.ShapeTable.func-eq
d_func'45'eq_82 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> Bool
d_func'45'eq_82 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C_K_8 v3
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_K_8 v4
                  -> coe d_ty'45'eq_84 (coe v3) (coe v4)
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
                       (coe d_func'45'eq_82 (coe v3) (coe v5))
                       (coe d_func'45'eq_82 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'8855'__14 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'8855'__14 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_func'45'eq_82 (coe v3) (coe v5))
                       (coe d_func'45'eq_82 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.ShapeTable.ty-eq
d_ty'45'eq_84 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Bool
d_ty'45'eq_84 v0 v1
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
                       (coe d_ty'45'eq_84 (coe v3) (coe v5))
                       (coe d_ty'45'eq_84 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'43'__22 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_84 (coe v3) (coe v5))
                       (coe d_ty'45'eq_84 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'8667'__24 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'8667'__24 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_84 (coe v3) (coe v5))
                       (coe d_ty'45'eq_84 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v4
                  -> coe d_func'45'eq_82 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v3
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v4
                  -> coe d_func'45'eq_82 (coe v3) (coe v4)
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
         MAlonzo.Code.Once.IRTy.C_Str_34
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_Str_34
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_Buffer_36
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_Buffer_36
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.nat-eq
d_nat'45'eq_138 :: Integer -> Integer -> Bool
d_nat'45'eq_138 v0 v1
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
                       coe (coe d_nat'45'eq_138 (coe v3) (coe v4))
                   _ -> coe v2))
-- Once.CCC.Codegen.ShapeTable.sub-reg
d_sub'45'reg_144 :: T_RegExpect_8 -> T_RegExpect_8 -> Bool
d_sub'45'reg_144 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v1 of
         C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_e'45'repr_12 v3
           -> case coe v0 of
                C_e'45'repr_12 v4 -> coe d_ty'45'eq_84 (coe v4) (coe v3)
                C_e'45'inl_14 v4 v5
                  -> coe
                       d_ty'45'eq_84
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v4) (coe v5)) (coe v3)
                C_e'45'inr_16 v4 v5
                  -> coe
                       d_ty'45'eq_84
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v4) (coe v5)) (coe v3)
                C_e'45'fresh_20 v4 v5
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
                                                          (coe d_ty'45'eq_84 (coe v7) (coe v10))
                                                          (coe d_ty'45'eq_84 (coe v9) (coe v11))
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
                                                            -> coe d_ty'45'eq_84 (coe v9) (coe v10)
                                                          _ -> coe v2
                                                   _ -> coe v2
                                            _ -> coe v2
                                     1 -> case coe v5 of
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                              -> case coe v8 of
                                                   C_e'45'repr_12 v9
                                                     -> case coe v3 of
                                                          MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
                                                            -> coe d_ty'45'eq_84 (coe v9) (coe v11)
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
                       (coe d_ty'45'eq_84 (coe v5) (coe v3))
                       (coe d_ty'45'eq_84 (coe v6) (coe v4))
                _ -> coe v2
         C_e'45'inr_16 v3 v4
           -> case coe v0 of
                C_e'45'inr_16 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_84 (coe v5) (coe v3))
                       (coe d_ty'45'eq_84 (coe v6) (coe v4))
                _ -> coe v2
         C_e'45'tag_18 v3
           -> case coe v0 of
                C_e'45'tag_18 v4 -> coe d_nat'45'eq_138 (coe v4) (coe v3)
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.sub-slots
d_sub'45'slots_202 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Bool
d_sub'45'slots_202 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       d_sub'45'reg_144 (coe d_slot'45'get_40 (coe v0) (coe v4)) (coe v5))
                    (coe d_sub'45'slots_202 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.sub-expect
d_sub'45'expect_214 :: T_Expect_24 -> T_Expect_24 -> Bool
d_sub'45'expect_214 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         d_sub'45'reg_144 (coe d_e'45'in1_32 (coe v0))
         (coe d_e'45'in1_32 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe
            d_sub'45'reg_144 (coe d_e'45'out_34 (coe v0))
            (coe d_e'45'out_34 (coe v1)))
         (coe
            d_sub'45'slots_202 (coe d_e'45'slot_36 (coe v0))
            (coe d_e'45'slot_36 (coe v1))))
-- Once.CCC.Codegen.ShapeTable.as-sum-of
d_as'45'sum'45'of_220 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_as'45'sum'45'of_220 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.as-sum-of-inv
d_as'45'sum'45'of'45'inv_232 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_as'45'sum'45'of'45'inv_232 = erased
-- Once.CCC.Codegen.ShapeTable.as-sum
d_as'45'sum_238 ::
  T_RegExpect_8 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_as'45'sum_238 v0
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
                       d_as'45'sum'45'of_220
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v2))
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v3
                  -> coe
                       d_as'45'sum'45'of_220
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v2))
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.is-ptr
d_is'45'ptr_248 :: T_RegExpect_8 -> Bool
d_is'45'ptr_248 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_e'45'repr_12 v2
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v3 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.IRTy.C__'43'__22 v3 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.IRTy.C__'8667'__24 v3 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         C_e'45'inl_14 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_e'45'inr_16 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_e'45'fresh_20 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.fst-of
d_fst'45'of_274 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_RegExpect_8
d_fst'45'of_274 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
           -> coe C_e'45'repr_12 (coe v2)
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.load-fst
d_load'45'fst_280 :: T_RegExpect_8 -> T_RegExpect_8
d_load'45'fst_280 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         C_e'45'repr_12 v2
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v3 v4
                  -> coe C_e'45'repr_12 (coe v3)
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
                  -> coe
                       d_fst'45'of_274
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v2))
                _ -> coe v1
         C_e'45'fresh_20 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v4
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.snd-of
d_snd'45'of_290 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_RegExpect_8
d_snd'45'of_290 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
           -> coe C_e'45'repr_12 (coe v3)
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.load-snd
d_load'45'snd_296 :: T_RegExpect_8 -> T_RegExpect_8
d_load'45'snd_296 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         C_e'45'repr_12 v2
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v3 v4
                  -> coe C_e'45'repr_12 (coe v4)
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
                  -> coe
                       d_snd'45'of_290
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v2))
                _ -> coe v1
         C_e'45'inl_14 v2 v3 -> coe C_e'45'repr_12 (coe v2)
         C_e'45'inr_16 v2 v3 -> coe C_e'45'repr_12 (coe v3)
         C_e'45'fresh_20 v2 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v4
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.step-expect
d_step'45'expect_314 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  T_Expect_24
d_step'45'expect_314 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2208
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1))
             (coe d_e'45'in1_32 (coe v1)) (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2210
        -> coe
             C_mkExpect_38 (coe d_e'45'out_34 (coe v1))
             (coe d_e'45'out_34 (coe v1)) (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2212
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1))
             (coe d_load'45'fst_280 (coe d_e'45'in1_32 (coe v1)))
             (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2214
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1))
             (coe d_load'45'snd_296 (coe d_e'45'in1_32 (coe v1)))
             (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2216 v3
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1))
             (coe d_slot'45'get_40 (coe d_e'45'slot_36 (coe v1)) (coe v3))
             (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2218 v3
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1))
             (coe d_e'45'out_34 (coe v1))
             (coe
                d_slot'45'put_72 (coe d_e'45'slot_36 (coe v1)) (coe v3)
                (coe d_e'45'out_34 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2220
        -> let v3 = d_e'45'in1_32 (coe v1) in
           coe
             (case coe v3 of
                C_e'45'fresh_20 v4 v5
                  -> coe
                       C_mkExpect_38
                       (coe
                          C_e'45'fresh_20
                          (coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe d_e'45'out_34 (coe v1)))
                          (coe v5))
                       (coe d_e'45'out_34 (coe v1)) (coe d_e'45'slot_36 (coe v1))
                _ -> coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2222
        -> let v3 = d_e'45'in1_32 (coe v1) in
           coe
             (case coe v3 of
                C_e'45'fresh_20 v4 v5
                  -> coe
                       C_mkExpect_38
                       (coe
                          C_e'45'fresh_20 (coe v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe d_e'45'out_34 (coe v1))))
                       (coe d_e'45'out_34 (coe v1)) (coe d_e'45'slot_36 (coe v1))
                _ -> coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2224 v3
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2226 v3
        -> coe
             C_mkExpect_38
             (coe d_slot'45'get_40 (coe d_e'45'slot_36 (coe v1)) (coe v3))
             (coe d_e'45'out_34 (coe v1)) (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2228 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2230 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2232 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2234 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2236
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2238
        -> coe
             C_mkExpect_38 (coe C_e'45'any_10) (coe C_e'45'any_10)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2240 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2242 v3
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1))
             (coe d_e'45'out_34 (coe v1))
             (coe
                d_slot'45'put_72 (coe d_e'45'slot_36 (coe v1)) (coe v3)
                (coe d_e'45'out_34 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2244 v3
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1))
             (coe d_slot'45'get_40 (coe d_e'45'slot_36 (coe v1)) (coe v3))
             (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2246 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2252 v3 v4 v5
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2256 v3 v4 v5
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2258 v3
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2260
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2262 v3
        -> coe
             C_mkExpect_38 (coe d_e'45'in1_32 (coe v1))
             (coe C_e'45'tag_18 (coe v3)) (coe d_e'45'slot_36 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2264 v3 v4
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2266 v3
        -> coe
             C_mkExpect_38
             (coe d_e'45'in1_32 (coe du_scrub'45'expect_510 (coe v1)))
             (coe
                C_e'45'fresh_20 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
             (coe d_e'45'slot_36 (coe du_scrub'45'expect_510 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2268 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2270 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2272 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2194 v4
               -> coe v0 v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2196 v4
               -> coe
                    C_mkExpect_38 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2198 v4
               -> coe v1
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2200 v4
               -> let v5 = d_e'45'in1_32 (coe v1) in
                  coe
                    (let v6
                           = let v6 = d_as'45'sum_238 (coe v5) in
                             coe
                               (case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                    -> case coe v7 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                           -> coe
                                                C_mkExpect_38 (coe C_e'45'inr_16 (coe v8) (coe v9))
                                                (coe d_e'45'out_34 (coe v1))
                                                (coe d_e'45'slot_36 (coe v1))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                                  _ -> MAlonzo.RTE.mazUnreachableError) in
                     coe
                       (case coe v5 of
                          C_e'45'fresh_20 v7 v8 -> coe v1
                          _ -> coe v6))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2202 v4 v5
               -> coe
                    C_mkExpect_38 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2204 v4
               -> coe
                    C_mkExpect_38 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2274 v3
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable._.scrub
d_scrub_498 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 -> Integer -> T_RegExpect_8 -> T_RegExpect_8
d_scrub_498 ~v0 ~v1 ~v2 v3 = du_scrub_498 v3
du_scrub_498 :: T_RegExpect_8 -> T_RegExpect_8
du_scrub_498 v0
  = case coe v0 of
      C_e'45'fresh_20 v1 v2 -> coe C_e'45'any_10
      _ -> coe v0
-- Once.CCC.Codegen.ShapeTable._.scrub-slots
d_scrub'45'slots_502 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_scrub'45'slots_502 ~v0 ~v1 ~v2 v3 = du_scrub'45'slots_502 v3
du_scrub'45'slots_502 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_scrub'45'slots_502 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe du_scrub_498 (coe v4)))
                    (coe du_scrub'45'slots_502 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable._.scrub-expect
d_scrub'45'expect_510 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 -> Integer -> T_Expect_24 -> T_Expect_24
d_scrub'45'expect_510 ~v0 ~v1 ~v2 v3 = du_scrub'45'expect_510 v3
du_scrub'45'expect_510 :: T_Expect_24 -> T_Expect_24
du_scrub'45'expect_510 v0
  = coe
      C_mkExpect_38 (coe du_scrub_498 (coe d_e'45'in1_32 (coe v0)))
      (coe du_scrub_498 (coe d_e'45'out_34 (coe v0)))
      (coe du_scrub'45'slots_502 (coe d_e'45'slot_36 (coe v0)))
-- Once.CCC.Codegen.ShapeTable.is-fresh
d_is'45'fresh_618 :: T_RegExpect_8 -> Bool
d_is'45'fresh_618 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_e'45'fresh_20 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.is-just
d_is'45'just_622 :: () -> Maybe AgdaAny -> Bool
d_is'45'just_622 ~v0 v1 = du_is'45'just_622 v1
du_is'45'just_622 :: Maybe AgdaAny -> Bool
du_is'45'just_622 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.tag-site-ok
d_tag'45'site'45'ok_624 :: T_RegExpect_8 -> Bool
d_tag'45'site'45'ok_624 v0
  = let v1 = coe du_is'45'just_622 (coe d_as'45'sum_238 (coe v0)) in
    coe
      (case coe v0 of
         C_e'45'fresh_20 v2 v3
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
d_not'45'any_632 :: T_RegExpect_8 -> Bool
d_not'45'any_632 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v0 of
         C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.site-ok
d_site'45'ok_634 ::
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 -> Bool
d_site'45'ok_634 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2212
           -> coe d_is'45'ptr_248 (coe d_e'45'in1_32 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2214
           -> coe d_is'45'ptr_248 (coe d_e'45'in1_32 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2216 v3
           -> coe
                d_not'45'any_632
                (coe d_slot'45'get_40 (coe d_e'45'slot_36 (coe v0)) (coe v3))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2220
           -> coe d_is'45'fresh_618 (coe d_e'45'in1_32 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2222
           -> coe d_is'45'fresh_618 (coe d_e'45'in1_32 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2226 v3
           -> coe
                d_not'45'any_632
                (coe d_slot'45'get_40 (coe d_e'45'slot_36 (coe v0)) (coe v3))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2244 v3
           -> coe
                d_not'45'any_632
                (coe d_slot'45'get_40 (coe d_e'45'slot_36 (coe v0)) (coe v3))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2272 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2200 v4
                  -> coe d_tag'45'site'45'ok_624 (coe d_e'45'in1_32 (coe v0))
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.ctrl-ok
d_ctrl'45'ok_662 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 -> Bool
d_ctrl'45'ok_662 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2272 v4
           -> case coe v4 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2194 v5
                  -> coe d_sub'45'expect_214 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2196 v5
                  -> coe d_sub'45'expect_214 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2198 v5
                  -> coe d_sub'45'expect_214 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2200 v5
                  -> let v6 = d_e'45'in1_32 (coe v1) in
                     coe
                       (let v7
                              = let v7 = d_as'45'sum_238 (coe v6) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                       -> case coe v8 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                              -> coe
                                                   d_sub'45'expect_214
                                                   (coe
                                                      C_mkExpect_38
                                                      (coe C_e'45'inl_14 (coe v9) (coe v10))
                                                      (coe d_e'45'out_34 (coe v1))
                                                      (coe d_e'45'slot_36 (coe v1)))
                                                   (coe v0 v5)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                     _ -> MAlonzo.RTE.mazUnreachableError) in
                        coe
                          (case coe v6 of
                             C_e'45'fresh_20 v8 v9
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> case coe v10 of
                                           C_e'45'tag_18 v11
                                             -> case coe v11 of
                                                  0 -> coe d_sub'45'expect_214 (coe v1) (coe v0 v5)
                                                  _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                           _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                             _ -> coe v7))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2202 v5 v6
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2204 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
-- Once.CCC.Codegen.ShapeTable.check-shapes
d_check'45'shapes_770 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] -> Bool
d_check'45'shapes_770 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_site'45'ok_634 (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe d_ctrl'45'ok_662 (coe v0) (coe v1) (coe v3))
                (coe
                   d_check'45'shapes_770 (coe v0)
                   (coe d_step'45'expect_314 (coe v0) (coe v1) (coe v3)) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.scan-expect
d_scan'45'expect_784 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  [T_Expect_24]
d_scan'45'expect_784 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe
                d_scan'45'expect_784 (coe v0)
                (coe d_step'45'expect_314 (coe v0) (coe v1) (coe v3)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.scan-length
d_scan'45'length_804 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scan'45'length_804 = erased
-- Once.CCC.Codegen.ShapeTable.post-expect
d_post'45'expect_822 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  T_Expect_24
d_post'45'expect_822 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4
        -> coe
             d_post'45'expect_822 (coe v0)
             (coe d_step'45'expect_314 (coe v0) (coe v1) (coe v3)) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.check-++
d_check'45''43''43'_844 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_check'45''43''43'_844 = erased
-- Once.CCC.Codegen.ShapeTable._.∧-assoc₂
d_'8743''45'assoc'8322'_874 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Bool ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc'8322'_874 = erased
-- Once.CCC.Codegen.ShapeTable.post-++
d_post'45''43''43'_902 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_post'45''43''43'_902 = erased
-- Once.CCC.Codegen.ShapeTable.IsHeap
d_IsHeap_920 :: MAlonzo.Code.Once.IR.T_AllocMode_4 -> ()
d_IsHeap_920 = erased
-- Once.CCC.Codegen.ShapeTable.HeapModed
d_HeapModed_926 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_HeapModed_926 = erased
-- Once.CCC.Codegen.ShapeTable.entry-expect
d_entry'45'expect_964 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_Expect_24
d_entry'45'expect_964 v0
  = coe
      C_mkExpect_38 (coe C_e'45'repr_12 (coe v0)) (coe C_e'45'any_10)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Codegen.ShapeTable.at-pc
d_at'45'pc_968 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206
d_at'45'pc_968 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_at'45'pc_968 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.state-at
d_state'45'at_982 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer -> T_Expect_24
d_state'45'at_982 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe v1
      (:) v4 v5
        -> case coe v3 of
             0 -> coe v1
             _ -> let v6 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       d_state'45'at_982 (coe v0)
                       (coe d_step'45'expect_314 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.∧-split
d_'8743''45'split_1012 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_1012 v0 v1 ~v2 = du_'8743''45'split_1012 v0 v1
du_'8743''45'split_1012 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_1012 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.CCC.Codegen.ShapeTable.check-at
d_check'45'at_1026 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'at_1026 v0 v1 v2 v3 ~v4 ~v5 ~v6
  = du_check'45'at_1026 v0 v1 v2 v3
du_check'45'at_1026 ::
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'at_1026 v0 v1 v2 v3
  = case coe v2 of
      (:) v4 v5
        -> case coe v3 of
             0 -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_'8743''45'split_1012 (coe d_site'45'ok_634 (coe v1) (coe v4))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                             (coe d_ctrl'45'ok_662 (coe v0) (coe v1) (coe v4))
                             (coe
                                d_check'45'shapes_770 (coe v0)
                                (coe d_step'45'expect_314 (coe v0) (coe v1) (coe v4)) (coe v5)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_'8743''45'split_1012
                          (coe d_ctrl'45'ok_662 (coe v0) (coe v1) (coe v4))
                          (coe
                             d_check'45'shapes_770 (coe v0)
                             (coe d_step'45'expect_314 (coe v0) (coe v1) (coe v4)) (coe v5))))
             _ -> let v6 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_check'45'at_1026 (coe v0)
                       (coe d_step'45'expect_314 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.readLoc
d_readLoc_1066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1066 ~v0 = du_readLoc_1066
du_readLoc_1066 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1066
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_632
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState
d_FlatState_1070 a0 = ()
-- Once.CCC.Codegen.ShapeTable.Sem._.fetch
d_fetch_1076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206
d_fetch_1076 ~v0 = du_fetch_1076
du_fetch_1076 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206
du_fetch_1076 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_214
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.falloc
d_falloc_1084 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_1084 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fclosure
d_fclosure_1086 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1086 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.flink
d_flink_1088 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1088 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.floc
d_floc_1090 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_1090 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fpc
d_fpc_1092 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1092 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fret
d_fret_1094 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1094 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.ShapeAt
d_ShapeAt_1098 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.ShapeTable.Sem._.TagAt
d_TagAt_1100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_TagAt_1100 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.BeforeFrontier
d_BeforeFrontier_1152 a0 a1 a2 = ()
-- Once.CCC.Codegen.ShapeTable.Sem.RegShape
d_RegShape_1168 a0 a1 a2 a3 a4 = ()
data T_RegShape_1168
  = C_rs'45'unit_1176 |
    C_rs'45'ptr_1184 MAlonzo.Code.Once.IR.T_AllocMode_4
                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 |
    C_rs'45'int_1188 | C_rs'45'float_1192
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt
d_InlAt_1204 a0 a1 a2 a3 a4 a5 = ()
data T_InlAt_1204
  = C_constructor_1252 MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-m
d_i'45'm_1234 :: T_InlAt_1204 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_i'45'm_1234 v0
  = case coe v0 of
      C_constructor_1252 v1 v2 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-mA
d_i'45'mA_1236 ::
  T_InlAt_1204 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_i'45'mA_1236 v0
  = case coe v0 of
      C_constructor_1252 v1 v2 v3 v4 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-payload
d_i'45'payload_1238 ::
  T_InlAt_1204 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_i'45'payload_1238 v0
  = case coe v0 of
      C_constructor_1252 v1 v2 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-mode
d_i'45'mode_1240 :: T_InlAt_1204 -> AgdaAny
d_i'45'mode_1240 v0
  = case coe v0 of
      C_constructor_1252 v1 v2 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-tag
d_i'45'tag_1242 :: T_InlAt_1204 -> AgdaAny
d_i'45'tag_1242 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-cell
d_i'45'cell_1244 ::
  T_InlAt_1204 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'45'cell_1244 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-bf-p
d_i'45'bf'45'p_1246 ::
  T_InlAt_1204 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_i'45'bf'45'p_1246 v0
  = case coe v0 of
      C_constructor_1252 v1 v2 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-bf-s
d_i'45'bf'45's_1248 ::
  T_InlAt_1204 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_i'45'bf'45's_1248 v0
  = case coe v0 of
      C_constructor_1252 v1 v2 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-pay
d_i'45'pay_1250 ::
  T_InlAt_1204 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_i'45'pay_1250 v0
  = case coe v0 of
      C_constructor_1252 v1 v2 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt
d_InrAt_1264 a0 a1 a2 a3 a4 a5 = ()
data T_InrAt_1264
  = C_constructor_1312 MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-m
d_r'45'm_1294 :: T_InrAt_1264 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_r'45'm_1294 v0
  = case coe v0 of
      C_constructor_1312 v1 v2 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-mB
d_r'45'mB_1296 ::
  T_InrAt_1264 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_r'45'mB_1296 v0
  = case coe v0 of
      C_constructor_1312 v1 v2 v3 v4 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-payload
d_r'45'payload_1298 ::
  T_InrAt_1264 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_r'45'payload_1298 v0
  = case coe v0 of
      C_constructor_1312 v1 v2 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-mode
d_r'45'mode_1300 :: T_InrAt_1264 -> AgdaAny
d_r'45'mode_1300 v0
  = case coe v0 of
      C_constructor_1312 v1 v2 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-tag
d_r'45'tag_1302 :: T_InrAt_1264 -> AgdaAny
d_r'45'tag_1302 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-cell
d_r'45'cell_1304 ::
  T_InrAt_1264 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r'45'cell_1304 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-bf-p
d_r'45'bf'45'p_1306 ::
  T_InrAt_1264 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_r'45'bf'45'p_1306 v0
  = case coe v0 of
      C_constructor_1312 v1 v2 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-bf-s
d_r'45'bf'45's_1308 ::
  T_InrAt_1264 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_r'45'bf'45's_1308 v0
  = case coe v0 of
      C_constructor_1312 v1 v2 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-pay
d_r'45'pay_1310 ::
  T_InrAt_1264 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_r'45'pay_1310 v0
  = case coe v0 of
      C_constructor_1312 v1 v2 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsR
d_MeetsR_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> ()
d_MeetsR_1314 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsCell
d_MeetsCell_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> ()
d_MeetsCell_1316 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MCell
d_MCell_1318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> ()
d_MCell_1318 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.FreshAt
d_FreshAt_1320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_RegExpect_8 ->
  Maybe T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> ()
d_FreshAt_1320 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsSlot
d_MeetsSlot_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> ()
d_MeetsSlot_1464 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.Meets
d_Meets_1554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Meets_1554 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.func-eq-sound
d_func'45'eq'45'sound_1566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_func'45'eq'45'sound_1566 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.ty-eq-sound
d_ty'45'eq'45'sound_1572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ty'45'eq'45'sound_1572 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.nat-eq-sound
d_nat'45'eq'45'sound_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'eq'45'sound_1710 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.inl-shape
d_inl'45'shape_1736 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_InlAt_1204 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_inl'45'shape_1736 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_inl'45'shape_1736 v5
du_inl'45'shape_1736 ::
  T_InlAt_1204 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
du_inl'45'shape_1736 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138
      (d_i'45'payload_1238 (coe v0)) (d_i'45'mA_1236 (coe v0))
      (d_i'45'mode_1240 (coe v0)) (d_i'45'bf'45'p_1246 (coe v0))
      (d_i'45'bf'45's_1248 (coe v0)) (d_i'45'pay_1250 (coe v0))
-- Once.CCC.Codegen.ShapeTable.Sem.inr-shape
d_inr'45'shape_1752 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_InrAt_1264 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_inr'45'shape_1752 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_inr'45'shape_1752 v5
du_inr'45'shape_1752 ::
  T_InrAt_1264 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
du_inr'45'shape_1752 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156
      (d_r'45'payload_1298 (coe v0)) (d_r'45'mB_1296 (coe v0))
      (d_r'45'mode_1300 (coe v0)) (d_r'45'bf'45'p_1306 (coe v0))
      (d_r'45'bf'45's_1308 (coe v0)) (d_r'45'pay_1310 (coe v0))
-- Once.CCC.Codegen.ShapeTable.Sem.sub-reg-sound
d_sub'45'reg'45'sound_1766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_sub'45'reg'45'sound_1766 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_sub'45'reg'45'sound_1766 v1 v2 v7
du_sub'45'reg'45'sound_1766 ::
  T_RegExpect_8 -> T_RegExpect_8 -> AgdaAny -> AgdaAny
du_sub'45'reg'45'sound_1766 v0 v1 v2
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
                                  C_rs'45'ptr_1184 (d_i'45'm_1234 (coe v9))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138
                                     (d_i'45'payload_1238 (coe v9)) (d_i'45'mA_1236 (coe v9))
                                     (d_i'45'mode_1240 (coe v9)) (d_i'45'bf'45'p_1246 (coe v9))
                                     (d_i'45'bf'45's_1248 (coe v9)) (d_i'45'pay_1250 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_e'45'inr_16 v4 v5
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> coe
                                  C_rs'45'ptr_1184 (d_r'45'm_1294 (coe v9))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156
                                     (d_r'45'payload_1298 (coe v9)) (d_r'45'mB_1296 (coe v9))
                                     (d_r'45'mode_1300 (coe v9)) (d_r'45'bf'45'p_1306 (coe v9))
                                     (d_r'45'bf'45's_1308 (coe v9)) (d_r'45'pay_1310 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_e'45'fresh_20 v4 v5
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
                                                                                                                                          C_rs'45'ptr_1184
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.IR.C_Heap_8)
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_98
                                                                                                                                             v19
                                                                                                                                             v27
                                                                                                                                             v25
                                                                                                                                             v33
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                             v23
                                                                                                                                             v31
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_668
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
                                                                                                                                             v26
                                                                                                                                             v34)
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
                                                                                                                     C_rs'45'ptr_1184
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.IR.C_Heap_8)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138
                                                                                                                        v19
                                                                                                                        v25
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                        v23
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_668
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
                                                                                                                     C_rs'45'ptr_1184
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.IR.C_Heap_8)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156
                                                                                                                        v19
                                                                                                                        v25
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                        v23
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_668
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
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.slot-just
d_slot'45'just_2018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny -> AgdaAny
d_slot'45'just_2018 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_slot'45'just_2018 v1 v5
du_slot'45'just_2018 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_slot'45'just_2018 v0 v1
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v2 -> coe v1
      C_e'45'inl_14 v2 v3 -> coe v1
      C_e'45'inr_16 v2 v3 -> coe v1
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'fresh_20 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.just-slot
d_just'45'slot_2040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny -> AgdaAny
d_just'45'slot_2040 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_just'45'slot_2040 v1 v5
du_just'45'slot_2040 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_just'45'slot_2040 v0 v1
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v2 -> coe v1
      C_e'45'inl_14 v2 v3 -> coe v1
      C_e'45'inr_16 v2 v3 -> coe v1
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'fresh_20 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.sub-slot-sound
d_sub'45'slot'45'sound_2064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_sub'45'slot'45'sound_2064 ~v0 v1 v2 ~v3 v4 ~v5 ~v6 v7
  = du_sub'45'slot'45'sound_2064 v1 v2 v4 v7
du_sub'45'slot'45'sound_2064 ::
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_sub'45'slot'45'sound_2064 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_just'45'slot_2040 (coe v1)
             (coe
                du_sub'45'reg'45'sound_1766 (coe v0) (coe v1)
                (coe du_slot'45'just_2018 (coe v0) (coe v3)))
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
             C_e'45'fresh_20 v4 v5
               -> coe
                    seq (coe v0) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.sub-slots-sound
d_sub'45'slots'45'sound_2198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'slots'45'sound_2198 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.sub-any
d_sub'45'any_2212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_RegExpect_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'any_2212 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.sub-expect-sound
d_sub'45'expect'45'sound_2260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Expect_24 ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sub'45'expect'45'sound_2260 ~v0 v1 v2 v3 ~v4 v5
  = du_sub'45'expect'45'sound_2260 v1 v2 v3 v5
du_sub'45'expect'45'sound_2260 ::
  T_Expect_24 ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sub'45'expect'45'sound_2260 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_sub'45'reg'45'sound_1766 (coe d_e'45'in1_32 (coe v0))
                       (coe d_e'45'in1_32 (coe v1)) (coe v4))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          du_sub'45'reg'45'sound_1766 (coe d_e'45'out_34 (coe v0))
                          (coe d_e'45'out_34 (coe v1)) (coe v6))
                       (coe
                          (\ v8 ->
                             coe
                               du_sub'45'slot'45'sound_2064
                               (coe d_slot'45'get_40 (coe d_e'45'slot_36 (coe v0)) (coe v8))
                               (coe d_slot'45'get_40 (coe d_e'45'slot_36 (coe v1)) (coe v8))
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
                                  (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v2))
                                  (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_568
                                     (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
                                  v8)
                               (coe v7 v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.site-slot-written
d_site'45'slot'45'written_2282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_site'45'slot'45'written_2282 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.site-load-ptr
d_site'45'load'45'ptr_2310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'load'45'ptr_2310 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'load'45'ptr_2310 v1 v3 v6
du_site'45'load'45'ptr_2310 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'load'45'ptr_2310 v0 v1 v2
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
      C_e'45'fresh_20 v3 v4
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
d_tag'45'of'45'shape_2392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'of'45'shape_2392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_tag'45'of'45'shape_2392 v7
du_tag'45'of'45'shape_2392 ::
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'of'45'shape_2392 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138 v6 v8 v9 v12 v13 v14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             erased
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156 v6 v8 v9 v12 v13 v14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.tag-of-μ
d_tag'45'of'45'μ_2438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'of'45'μ_2438 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_tag'45'of'45'μ_2438 v5 v9
du_tag'45'of'45'μ_2438 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'of'45'μ_2438 v0 v1
  = coe seq (coe v0) (coe du_tag'45'of'45'shape_2392 (coe v1))
-- Once.CCC.Codegen.ShapeTable.Sem.site-branch-tag
d_site'45'branch'45'tag_2458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'branch'45'tag_2458 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'branch'45'tag_2458 v1 v3 v6
du_site'45'branch'45'tag_2458 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'branch'45'tag_2458 v0 v1 v2
  = case coe v0 of
      C_e'45'repr_12 v3
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v4 v5
               -> case coe v2 of
                    C_rs'45'ptr_1184 v7 v9
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                     (coe du_tag'45'of'45'shape_2392 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v4
               -> case coe v2 of
                    C_rs'45'ptr_1184 v6 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_170 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe
                                               du_go_2534
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                  (coe v4) (coe v3))
                                               (coe
                                                  d_as'45'sum'45'of_220
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                     (coe v4) (coe v3)))
                                               (coe v16)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v4
               -> case coe v2 of
                    C_rs'45'ptr_1184 v6 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'ν_184 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe
                                               du_go_2582
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                  (coe v4) (coe v3))
                                               (coe
                                                  d_as'45'sum'45'of_220
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
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
      C_e'45'fresh_20 v3 v4
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
d_go_2534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2534 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17
  = du_go_2534 v9 v10 v17
du_go_2534 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2534 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe seq (coe v3) (coe du_tag'45'of'45'μ_2438 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.go
d_go_2582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17
  = du_go_2582 v9 v10 v17
du_go_2582 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2582 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe seq (coe v3) (coe du_tag'45'of'45'μ_2438 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.writeHeapMem-aux
d_writeHeapMem'45'aux_2624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem'45'aux_2624 ~v0 = du_writeHeapMem'45'aux_2624
du_writeHeapMem'45'aux_2624 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem'45'aux_2624 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_764 v2
      v3 v4
-- Once.CCC.Codegen.ShapeTable.Sem._.writeLocToHeap
d_writeLocToHeap_2626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToHeap_2626 ~v0 = du_writeLocToHeap_2626
du_writeLocToHeap_2626 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToHeap_2626
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_790
-- Once.CCC.Codegen.ShapeTable.Sem.nothing≢just
d_nothing'8802'just_2632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_2632 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.read-uw
d_read'45'uw_2644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'uw_2644 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.go
d_go_2680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_2680 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.tag-uw
d_tag'45'uw_2694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_tag'45'uw_2694 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.shape-uw
d_shape'45'uw_2738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_shape'45'uw_2738 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_shape'45'uw_2738 v3 v9
du_shape'45'uw_2738 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
du_shape'45'uw_2738 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'unit_76
        -> coe MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'unit_76
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_98 v7 v8 v10 v11 v12 v15 v16 v17 v18 v19
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v20 v21
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_98 v7 v8 v10
                    v11 v12 v15 v16 v17 (coe du_shape'45'uw_2738 (coe v20) (coe v18))
                    (coe du_shape'45'uw_2738 (coe v21) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure_120 v3 v8 v10 v11 v12 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure_120 v3 v8
             v10 v11 v12 v15 v16 (coe du_shape'45'uw_2738 (coe v3) (coe v17))
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138 v7 v9 v10 v13 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v16 v17
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138 v7 v9 v10
                    v13 v14 (coe du_shape'45'uw_2738 (coe v16) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156 v7 v9 v10 v13 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v16 v17
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156 v7 v9 v10
                    v13 v14 (coe du_shape'45'uw_2738 (coe v17) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_170 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_170 v7
                    (coe
                       du_shape'45'uw_2738
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v0))
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'ν_184 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'ν_184 v7
                    (coe
                       du_shape'45'uw_2738
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v0))
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'int_196 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'int_196 v6 v7
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'float_208 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'float_208 v6 v7
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'str_218 v6
        -> coe MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'str_218 v6
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'buffer_228 v6
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'buffer_228 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.meets-cell-uw
d_meets'45'cell'45'uw_2920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_meets'45'cell'45'uw_2920 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                           ~v10
  = du_meets'45'cell'45'uw_2920 v1 v8
du_meets'45'cell'45'uw_2920 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_meets'45'cell'45'uw_2920 v0 v1
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v9)
                                                  (coe du_shape'45'uw_2738 (coe v2) (coe v10)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'inl_14 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                        (coe du_inl'45'uw_2974 (coe v2) (coe v9))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'inr_16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                        (coe du_inr'45'uw_3014 (coe v3) (coe v9))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'fresh_20 v2 v3
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.inl-uw
d_inl'45'uw_2974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_InlAt_1204 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_InlAt_1204 -> T_InlAt_1204
d_inl'45'uw_2974 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16
  = du_inl'45'uw_2974 v1 v16
du_inl'45'uw_2974 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InlAt_1204 -> T_InlAt_1204
du_inl'45'uw_2974 v0 v1
  = case coe v1 of
      C_constructor_1252 v2 v3 v4 v5 v8 v9 v10
        -> coe
             C_constructor_1252 v2 v3 v4 v5 v8 v9
             (coe du_shape'45'uw_2738 (coe v0) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.inr-uw
d_inr'45'uw_3014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_InrAt_1264 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_InrAt_1264 -> T_InrAt_1264
d_inr'45'uw_3014 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16
  = du_inr'45'uw_3014 v2 v16
du_inr'45'uw_3014 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InrAt_1264 -> T_InrAt_1264
du_inr'45'uw_3014 v0 v1
  = case coe v1 of
      C_constructor_1312 v2 v3 v4 v5 v8 v9 v10
        -> coe
             C_constructor_1312 v2 v3 v4 v5 v8 v9
             (coe du_shape'45'uw_2738 (coe v0) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.fetch-at-pc
d_fetch'45'at'45'pc_3056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2206] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'pc_3056 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.fresh⇒ptr
d_fresh'8658'ptr_3072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fresh'8658'ptr_3072 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.site-store-ptr
d_site'45'store'45'ptr_3086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'store'45'ptr_3086 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'store'45'ptr_3086 v1 v3 v6
du_site'45'store'45'ptr_3086 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'store'45'ptr_3086 v0 v1 v2
  = coe du_site'45'load'45'ptr_2310 (coe v0) (coe v1) (coe v2)
