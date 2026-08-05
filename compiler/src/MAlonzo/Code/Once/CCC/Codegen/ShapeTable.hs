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
import qualified MAlonzo.Code.Agda.Builtin.Float
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
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Machine.ShapeAt
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
  = C_mkExpect_42 T_RegExpect_8 T_RegExpect_8 T_RegExpect_8
                  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.CCC.Codegen.ShapeTable.Expect.e-in1
d_e'45'in1_34 :: T_Expect_24 -> T_RegExpect_8
d_e'45'in1_34 v0
  = case coe v0 of
      C_mkExpect_42 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Expect.e-in2
d_e'45'in2_36 :: T_Expect_24 -> T_RegExpect_8
d_e'45'in2_36 v0
  = case coe v0 of
      C_mkExpect_42 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Expect.e-out
d_e'45'out_38 :: T_Expect_24 -> T_RegExpect_8
d_e'45'out_38 v0
  = case coe v0 of
      C_mkExpect_42 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Expect.e-slot
d_e'45'slot_40 ::
  T_Expect_24 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_e'45'slot_40 v0
  = case coe v0 of
      C_mkExpect_42 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.slot-get
d_slot'45'get_44 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_RegExpect_8
d_slot'45'get_44 v0 v1
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
                              else coe seq (coe v8) (coe d_slot'45'get_44 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.slot-put
d_slot'45'put_76 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  T_RegExpect_8 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_slot'45'put_76 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.CCC.Codegen.ShapeTable.LabelEnv
d_LabelEnv_84 :: ()
d_LabelEnv_84 = erased
-- Once.CCC.Codegen.ShapeTable.func-eq
d_func'45'eq_86 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> Bool
d_func'45'eq_86 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C_K_8 v3
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_K_8 v4
                  -> coe d_ty'45'eq_88 (coe v3) (coe v4)
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
                       (coe d_func'45'eq_86 (coe v3) (coe v5))
                       (coe d_func'45'eq_86 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'8855'__14 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'8855'__14 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_func'45'eq_86 (coe v3) (coe v5))
                       (coe d_func'45'eq_86 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.ShapeTable.ty-eq
d_ty'45'eq_88 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Bool
d_ty'45'eq_88 v0 v1
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
                       (coe d_ty'45'eq_88 (coe v3) (coe v5))
                       (coe d_ty'45'eq_88 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'43'__22 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_88 (coe v3) (coe v5))
                       (coe d_ty'45'eq_88 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C__'8667'__24 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'8667'__24 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_88 (coe v3) (coe v5))
                       (coe d_ty'45'eq_88 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v4
                  -> coe d_func'45'eq_86 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v3
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v4
                  -> coe d_func'45'eq_86 (coe v3) (coe v4)
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
d_nat'45'eq_142 :: Integer -> Integer -> Bool
d_nat'45'eq_142 v0 v1
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
                       coe (coe d_nat'45'eq_142 (coe v3) (coe v4))
                   _ -> coe v2))
-- Once.CCC.Codegen.ShapeTable.sub-reg
d_sub'45'reg_148 :: T_RegExpect_8 -> T_RegExpect_8 -> Bool
d_sub'45'reg_148 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v1 of
         C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_e'45'repr_12 v3
           -> case coe v0 of
                C_e'45'repr_12 v4 -> coe d_ty'45'eq_88 (coe v4) (coe v3)
                C_e'45'inl_14 v4 v5
                  -> coe
                       d_ty'45'eq_88
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v4) (coe v5)) (coe v3)
                C_e'45'inr_16 v4 v5
                  -> coe
                       d_ty'45'eq_88
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
                                                          (coe d_ty'45'eq_88 (coe v7) (coe v10))
                                                          (coe d_ty'45'eq_88 (coe v9) (coe v11))
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
                                                            -> coe d_ty'45'eq_88 (coe v9) (coe v10)
                                                          _ -> coe v2
                                                   _ -> coe v2
                                            _ -> coe v2
                                     1 -> case coe v5 of
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                              -> case coe v8 of
                                                   C_e'45'repr_12 v9
                                                     -> case coe v3 of
                                                          MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
                                                            -> coe d_ty'45'eq_88 (coe v9) (coe v11)
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
                       (coe d_ty'45'eq_88 (coe v5) (coe v3))
                       (coe d_ty'45'eq_88 (coe v6) (coe v4))
                _ -> coe v2
         C_e'45'inr_16 v3 v4
           -> case coe v0 of
                C_e'45'inr_16 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_ty'45'eq_88 (coe v5) (coe v3))
                       (coe d_ty'45'eq_88 (coe v6) (coe v4))
                _ -> coe v2
         C_e'45'tag_18 v3
           -> case coe v0 of
                C_e'45'tag_18 v4 -> coe d_nat'45'eq_142 (coe v4) (coe v3)
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.sub-slots
d_sub'45'slots_206 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Bool
d_sub'45'slots_206 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       d_sub'45'reg_148 (coe d_slot'45'get_44 (coe v0) (coe v4)) (coe v5))
                    (coe d_sub'45'slots_206 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.sub-expect
d_sub'45'expect_218 :: T_Expect_24 -> T_Expect_24 -> Bool
d_sub'45'expect_218 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         d_sub'45'reg_148 (coe d_e'45'in1_34 (coe v0))
         (coe d_e'45'in1_34 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe
            d_sub'45'reg_148 (coe d_e'45'in2_36 (coe v0))
            (coe d_e'45'in2_36 (coe v1)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe
               d_sub'45'reg_148 (coe d_e'45'out_38 (coe v0))
               (coe d_e'45'out_38 (coe v1)))
            (coe
               d_sub'45'slots_206 (coe d_e'45'slot_40 (coe v0))
               (coe d_e'45'slot_40 (coe v1)))))
-- Once.CCC.Codegen.ShapeTable.as-sum-of
d_as'45'sum'45'of_224 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_as'45'sum'45'of_224 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.as-sum-of-inv
d_as'45'sum'45'of'45'inv_236 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_as'45'sum'45'of'45'inv_236 = erased
-- Once.CCC.Codegen.ShapeTable.as-sum
d_as'45'sum_242 ::
  T_RegExpect_8 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_as'45'sum_242 v0
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
                       d_as'45'sum'45'of_224
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v2))
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v3
                  -> coe
                       d_as'45'sum'45'of_224
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v2))
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.is-ptr
d_is'45'ptr_252 :: T_RegExpect_8 -> Bool
d_is'45'ptr_252 v0
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
d_fst'45'of_278 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_RegExpect_8
d_fst'45'of_278 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
           -> coe C_e'45'repr_12 (coe v2)
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.load-fst
d_load'45'fst_284 :: T_RegExpect_8 -> T_RegExpect_8
d_load'45'fst_284 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         C_e'45'repr_12 v2
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v3 v4
                  -> coe C_e'45'repr_12 (coe v3)
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
                  -> coe
                       d_fst'45'of_278
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v2))
                _ -> coe v1
         C_e'45'fresh_20 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v4
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.snd-of
d_snd'45'of_294 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_RegExpect_8
d_snd'45'of_294 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
           -> coe C_e'45'repr_12 (coe v3)
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.load-snd
d_load'45'snd_300 :: T_RegExpect_8 -> T_RegExpect_8
d_load'45'snd_300 v0
  = let v1 = coe C_e'45'any_10 in
    coe
      (case coe v0 of
         C_e'45'repr_12 v2
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v3 v4
                  -> coe C_e'45'repr_12 (coe v4)
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
                  -> coe
                       d_snd'45'of_294
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
d_step'45'expect_318 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_Expect_24
d_step'45'expect_318 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe
             C_mkExpect_42 (coe d_e'45'out_38 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'out_38 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'in2_36 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1))
             (coe d_load'45'fst_284 (coe d_e'45'in1_34 (coe v1)))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1))
             (coe d_load'45'snd_300 (coe d_e'45'in1_34 (coe v1)))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1))
             (coe d_slot'45'get_44 (coe d_e'45'slot_40 (coe v1)) (coe v3))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe
                d_slot'45'put_76 (coe d_e'45'slot_40 (coe v1)) (coe v3)
                (coe d_e'45'out_38 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> let v3 = d_e'45'in1_34 (coe v1) in
           coe
             (case coe v3 of
                C_e'45'fresh_20 v4 v5
                  -> coe
                       C_mkExpect_42
                       (coe
                          C_e'45'fresh_20
                          (coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe d_e'45'out_38 (coe v1)))
                          (coe v5))
                       (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
                       (coe d_e'45'slot_40 (coe v1))
                _ -> coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> let v3 = d_e'45'in1_34 (coe v1) in
           coe
             (case coe v3 of
                C_e'45'fresh_20 v4 v5
                  -> coe
                       C_mkExpect_42
                       (coe
                          C_e'45'fresh_20 (coe v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe d_e'45'out_38 (coe v1))))
                       (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
                       (coe d_e'45'slot_40 (coe v1))
                _ -> coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v3
        -> coe
             C_mkExpect_42
             (coe d_slot'45'get_44 (coe d_e'45'slot_40 (coe v1)) (coe v3))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2214 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2216 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2220 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2222
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe
             C_mkExpect_42 (coe C_e'45'any_10) (coe C_e'45'any_10)
             (coe C_e'45'any_10)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe
                d_slot'45'put_76 (coe d_e'45'slot_40 (coe v1)) (coe v3)
                (coe d_e'45'out_38 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1))
             (coe d_slot'45'get_44 (coe d_e'45'slot_40 (coe v1)) (coe v3))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v3 v4 v5
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v3 v4 v5
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'tag_18 (coe v3))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2250 v3 v4
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v3
        -> coe
             C_mkExpect_42
             (coe d_e'45'in1_34 (coe du_scrub'45'expect_522 (coe v1)))
             (coe d_e'45'in2_36 (coe du_scrub'45'expect_522 (coe v1)))
             (coe
                C_e'45'fresh_20 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
             (coe d_e'45'slot_40 (coe du_scrub'45'expect_522 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2254 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v4
               -> coe v0 v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v4
               -> coe
                    C_mkExpect_42 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v4
               -> coe v1
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v4
               -> let v5 = d_e'45'in1_34 (coe v1) in
                  coe
                    (let v6
                           = let v6 = d_as'45'sum_242 (coe v5) in
                             coe
                               (case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                    -> case coe v7 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                           -> coe
                                                C_mkExpect_42 (coe C_e'45'inr_16 (coe v8) (coe v9))
                                                (coe d_e'45'in2_36 (coe v1))
                                                (coe d_e'45'out_38 (coe v1))
                                                (coe d_e'45'slot_40 (coe v1))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                                  _ -> MAlonzo.RTE.mazUnreachableError) in
                     coe
                       (case coe v5 of
                          C_e'45'fresh_20 v7 v8 -> coe v1
                          _ -> coe v6))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v4 v5
               -> coe
                    C_mkExpect_42 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v4
               -> coe
                    C_mkExpect_42 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2260 v3
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable._.scrub
d_scrub_510 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 -> Integer -> T_RegExpect_8 -> T_RegExpect_8
d_scrub_510 ~v0 ~v1 ~v2 v3 = du_scrub_510 v3
du_scrub_510 :: T_RegExpect_8 -> T_RegExpect_8
du_scrub_510 v0
  = case coe v0 of
      C_e'45'fresh_20 v1 v2 -> coe C_e'45'any_10
      _ -> coe v0
-- Once.CCC.Codegen.ShapeTable._.scrub-slots
d_scrub'45'slots_514 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_scrub'45'slots_514 ~v0 ~v1 ~v2 v3 = du_scrub'45'slots_514 v3
du_scrub'45'slots_514 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_scrub'45'slots_514 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe du_scrub_510 (coe v4)))
                    (coe du_scrub'45'slots_514 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable._.scrub-expect
d_scrub'45'expect_522 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 -> Integer -> T_Expect_24 -> T_Expect_24
d_scrub'45'expect_522 ~v0 ~v1 ~v2 v3 = du_scrub'45'expect_522 v3
du_scrub'45'expect_522 :: T_Expect_24 -> T_Expect_24
du_scrub'45'expect_522 v0
  = coe
      C_mkExpect_42 (coe du_scrub_510 (coe d_e'45'in1_34 (coe v0)))
      (coe du_scrub_510 (coe d_e'45'in2_36 (coe v0)))
      (coe du_scrub_510 (coe d_e'45'out_38 (coe v0)))
      (coe du_scrub'45'slots_514 (coe d_e'45'slot_40 (coe v0)))
-- Once.CCC.Codegen.ShapeTable.is-fresh
d_is'45'fresh_630 :: T_RegExpect_8 -> Bool
d_is'45'fresh_630 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_e'45'fresh_20 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.is-just
d_is'45'just_634 :: () -> Maybe AgdaAny -> Bool
d_is'45'just_634 ~v0 v1 = du_is'45'just_634 v1
du_is'45'just_634 :: Maybe AgdaAny -> Bool
du_is'45'just_634 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.tag-site-ok
d_tag'45'site'45'ok_636 :: T_RegExpect_8 -> Bool
d_tag'45'site'45'ok_636 v0
  = let v1 = coe du_is'45'just_634 (coe d_as'45'sum_242 (coe v0)) in
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
-- Once.CCC.Codegen.ShapeTable.site-ok
d_site'45'ok_644 ::
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> Bool
d_site'45'ok_644 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
           -> coe d_is'45'ptr_252 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
           -> coe d_is'45'ptr_252 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
           -> coe d_is'45'fresh_630 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
           -> coe d_is'45'fresh_630 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v4
                  -> coe d_tag'45'site'45'ok_636 (coe d_e'45'in1_34 (coe v0))
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.ctrl-ok
d_ctrl'45'ok_660 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> Bool
d_ctrl'45'ok_660 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v4
           -> case coe v4 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v5
                  -> coe d_sub'45'expect_218 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v5
                  -> coe d_sub'45'expect_218 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v5
                  -> coe d_sub'45'expect_218 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v5
                  -> let v6 = d_e'45'in1_34 (coe v1) in
                     coe
                       (let v7
                              = let v7 = d_as'45'sum_242 (coe v6) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                       -> case coe v8 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                              -> coe
                                                   d_sub'45'expect_218
                                                   (coe
                                                      C_mkExpect_42
                                                      (coe C_e'45'inl_14 (coe v9) (coe v10))
                                                      (coe d_e'45'in2_36 (coe v1))
                                                      (coe d_e'45'out_38 (coe v1))
                                                      (coe d_e'45'slot_40 (coe v1)))
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
                                                  0 -> coe d_sub'45'expect_218 (coe v1) (coe v0 v5)
                                                  _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                           _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                             _ -> coe v7))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v5 v6
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
-- Once.CCC.Codegen.ShapeTable.check-shapes
d_check'45'shapes_768 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> Bool
d_check'45'shapes_768 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_site'45'ok_644 (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe d_ctrl'45'ok_660 (coe v0) (coe v1) (coe v3))
                (coe
                   d_check'45'shapes_768 (coe v0)
                   (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v3)) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.scan-expect
d_scan'45'expect_782 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [T_Expect_24]
d_scan'45'expect_782 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe
                d_scan'45'expect_782 (coe v0)
                (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v3)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.scan-length
d_scan'45'length_802 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scan'45'length_802 = erased
-- Once.CCC.Codegen.ShapeTable.post-expect
d_post'45'expect_820 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_Expect_24
d_post'45'expect_820 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4
        -> coe
             d_post'45'expect_820 (coe v0)
             (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v3)) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.check-++
d_check'45''43''43'_842 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_check'45''43''43'_842 = erased
-- Once.CCC.Codegen.ShapeTable._.∧-assoc₂
d_'8743''45'assoc'8322'_872 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Bool ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc'8322'_872 = erased
-- Once.CCC.Codegen.ShapeTable.post-++
d_post'45''43''43'_900 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_post'45''43''43'_900 = erased
-- Once.CCC.Codegen.ShapeTable.IsHeap
d_IsHeap_918 :: MAlonzo.Code.Once.IR.T_AllocMode_4 -> ()
d_IsHeap_918 = erased
-- Once.CCC.Codegen.ShapeTable.HeapModed
d_HeapModed_924 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_HeapModed_924 = erased
-- Once.CCC.Codegen.ShapeTable.entry-expect
d_entry'45'expect_962 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_Expect_24
d_entry'45'expect_962 v0
  = coe
      C_mkExpect_42 (coe C_e'45'repr_12 (coe v0)) (coe C_e'45'any_10)
      (coe C_e'45'any_10)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Codegen.ShapeTable.at-pc
d_at'45'pc_966 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_at'45'pc_966 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_at'45'pc_966 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.state-at
d_state'45'at_980 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> T_Expect_24
d_state'45'at_980 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe v1
      (:) v4 v5
        -> case coe v3 of
             0 -> coe v1
             _ -> let v6 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       d_state'45'at_980 (coe v0)
                       (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.∧-split
d_'8743''45'split_1010 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_1010 v0 v1 ~v2 = du_'8743''45'split_1010 v0 v1
du_'8743''45'split_1010 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_1010 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.CCC.Codegen.ShapeTable.check-at
d_check'45'at_1024 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'at_1024 v0 v1 v2 v3 ~v4 ~v5 ~v6
  = du_check'45'at_1024 v0 v1 v2 v3
du_check'45'at_1024 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'at_1024 v0 v1 v2 v3
  = case coe v2 of
      (:) v4 v5
        -> case coe v3 of
             0 -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_'8743''45'split_1010 (coe d_site'45'ok_644 (coe v1) (coe v4))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                             (coe d_ctrl'45'ok_660 (coe v0) (coe v1) (coe v4))
                             (coe
                                d_check'45'shapes_768 (coe v0)
                                (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v4)) (coe v5)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_'8743''45'split_1010
                          (coe d_ctrl'45'ok_660 (coe v0) (coe v1) (coe v4))
                          (coe
                             d_check'45'shapes_768 (coe v0)
                             (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v4)) (coe v5))))
             _ -> let v6 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_check'45'at_1024 (coe v0)
                       (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.readLoc
d_readLoc_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_1064 ~v0 = du_readLoc_1064
du_readLoc_1064 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_1064
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState
d_FlatState_1068 a0 = ()
-- Once.CCC.Codegen.ShapeTable.Sem._.fetch
d_fetch_1074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch_1074 ~v0 = du_fetch_1074
du_fetch_1074 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch_1074 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.falloc
d_falloc_1082 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_1082 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fclosure
d_fclosure_1084 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_1084 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.floc
d_floc_1086 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_1086 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fpc
d_fpc_1088 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_1088 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fret
d_fret_1090 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_1090 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.ShapeAt
d_ShapeAt_1094 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.ShapeTable.Sem._.TagAt
d_TagAt_1096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_TagAt_1096 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.BeforeFrontier
d_BeforeFrontier_1148 a0 a1 a2 = ()
-- Once.CCC.Codegen.ShapeTable.Sem.RegShape
d_RegShape_1164 a0 a1 a2 a3 a4 = ()
data T_RegShape_1164
  = C_rs'45'unit_1172 |
    C_rs'45'ptr_1180 MAlonzo.Code.Once.IR.T_AllocMode_4
                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 |
    C_rs'45'int_1184 | C_rs'45'float_1188
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt
d_InlAt_1200 a0 a1 a2 a3 a4 a5 = ()
data T_InlAt_1200
  = C_constructor_1248 MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-m
d_i'45'm_1230 :: T_InlAt_1200 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_i'45'm_1230 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-mA
d_i'45'mA_1232 ::
  T_InlAt_1200 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_i'45'mA_1232 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-payload
d_i'45'payload_1234 ::
  T_InlAt_1200 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_i'45'payload_1234 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-mode
d_i'45'mode_1236 :: T_InlAt_1200 -> AgdaAny
d_i'45'mode_1236 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-tag
d_i'45'tag_1238 :: T_InlAt_1200 -> AgdaAny
d_i'45'tag_1238 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-cell
d_i'45'cell_1240 ::
  T_InlAt_1200 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'45'cell_1240 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-bf-p
d_i'45'bf'45'p_1242 ::
  T_InlAt_1200 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_i'45'bf'45'p_1242 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-bf-s
d_i'45'bf'45's_1244 ::
  T_InlAt_1200 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_i'45'bf'45's_1244 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-pay
d_i'45'pay_1246 ::
  T_InlAt_1200 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_i'45'pay_1246 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt
d_InrAt_1260 a0 a1 a2 a3 a4 a5 = ()
data T_InrAt_1260
  = C_constructor_1308 MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-m
d_r'45'm_1290 :: T_InrAt_1260 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_r'45'm_1290 v0
  = case coe v0 of
      C_constructor_1308 v1 v2 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-mB
d_r'45'mB_1292 ::
  T_InrAt_1260 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_r'45'mB_1292 v0
  = case coe v0 of
      C_constructor_1308 v1 v2 v3 v4 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-payload
d_r'45'payload_1294 ::
  T_InrAt_1260 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_r'45'payload_1294 v0
  = case coe v0 of
      C_constructor_1308 v1 v2 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-mode
d_r'45'mode_1296 :: T_InrAt_1260 -> AgdaAny
d_r'45'mode_1296 v0
  = case coe v0 of
      C_constructor_1308 v1 v2 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-tag
d_r'45'tag_1298 :: T_InrAt_1260 -> AgdaAny
d_r'45'tag_1298 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-cell
d_r'45'cell_1300 ::
  T_InrAt_1260 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r'45'cell_1300 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-bf-p
d_r'45'bf'45'p_1302 ::
  T_InrAt_1260 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_r'45'bf'45'p_1302 v0
  = case coe v0 of
      C_constructor_1308 v1 v2 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-bf-s
d_r'45'bf'45's_1304 ::
  T_InrAt_1260 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_r'45'bf'45's_1304 v0
  = case coe v0 of
      C_constructor_1308 v1 v2 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-pay
d_r'45'pay_1306 ::
  T_InrAt_1260 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_r'45'pay_1306 v0
  = case coe v0 of
      C_constructor_1308 v1 v2 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsR
d_MeetsR_1310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> ()
d_MeetsR_1310 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsCell
d_MeetsCell_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> ()
d_MeetsCell_1312 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MCell
d_MCell_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> ()
d_MCell_1314 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.FreshAt
d_FreshAt_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_RegExpect_8 ->
  Maybe T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> ()
d_FreshAt_1316 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsSlot
d_MeetsSlot_1460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> ()
d_MeetsSlot_1460 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.Meets
d_Meets_1550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_Meets_1550 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.func-eq-sound
d_func'45'eq'45'sound_1562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_func'45'eq'45'sound_1562 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.ty-eq-sound
d_ty'45'eq'45'sound_1568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ty'45'eq'45'sound_1568 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.nat-eq-sound
d_nat'45'eq'45'sound_1706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'eq'45'sound_1706 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.inl-shape
d_inl'45'shape_1732 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_InlAt_1200 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_inl'45'shape_1732 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_inl'45'shape_1732 v5
du_inl'45'shape_1732 ::
  T_InlAt_1200 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
du_inl'45'shape_1732 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138
      (d_i'45'payload_1234 (coe v0)) (d_i'45'mA_1232 (coe v0))
      (d_i'45'mode_1236 (coe v0)) (d_i'45'bf'45'p_1242 (coe v0))
      (d_i'45'bf'45's_1244 (coe v0)) (d_i'45'pay_1246 (coe v0))
-- Once.CCC.Codegen.ShapeTable.Sem.inr-shape
d_inr'45'shape_1748 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_InrAt_1260 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_inr'45'shape_1748 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_inr'45'shape_1748 v5
du_inr'45'shape_1748 ::
  T_InrAt_1260 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
du_inr'45'shape_1748 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156
      (d_r'45'payload_1294 (coe v0)) (d_r'45'mB_1292 (coe v0))
      (d_r'45'mode_1296 (coe v0)) (d_r'45'bf'45'p_1302 (coe v0))
      (d_r'45'bf'45's_1304 (coe v0)) (d_r'45'pay_1306 (coe v0))
-- Once.CCC.Codegen.ShapeTable.Sem.sub-reg-sound
d_sub'45'reg'45'sound_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_sub'45'reg'45'sound_1762 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_sub'45'reg'45'sound_1762 v1 v2 v7
du_sub'45'reg'45'sound_1762 ::
  T_RegExpect_8 -> T_RegExpect_8 -> AgdaAny -> AgdaAny
du_sub'45'reg'45'sound_1762 v0 v1 v2
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
                                  C_rs'45'ptr_1180 (d_i'45'm_1230 (coe v9))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138
                                     (d_i'45'payload_1234 (coe v9)) (d_i'45'mA_1232 (coe v9))
                                     (d_i'45'mode_1236 (coe v9)) (d_i'45'bf'45'p_1242 (coe v9))
                                     (d_i'45'bf'45's_1244 (coe v9)) (d_i'45'pay_1246 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_e'45'inr_16 v4 v5
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> coe
                                  C_rs'45'ptr_1180 (d_r'45'm_1290 (coe v9))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156
                                     (d_r'45'payload_1294 (coe v9)) (d_r'45'mB_1292 (coe v9))
                                     (d_r'45'mode_1296 (coe v9)) (d_r'45'bf'45'p_1302 (coe v9))
                                     (d_r'45'bf'45's_1304 (coe v9)) (d_r'45'pay_1306 (coe v9)))
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
                                                                                                                                          C_rs'45'ptr_1180
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
                                                                                                                                                MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_656
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
                                                                                                                     C_rs'45'ptr_1180
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
                                                                                                                           MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_656
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
                                                                                                                     C_rs'45'ptr_1180
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
                                                                                                                           MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_656
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
d_slot'45'just_2014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny -> AgdaAny
d_slot'45'just_2014 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_slot'45'just_2014 v1 v5
du_slot'45'just_2014 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_slot'45'just_2014 v0 v1
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v2 -> coe v1
      C_e'45'inl_14 v2 v3 -> coe v1
      C_e'45'inr_16 v2 v3 -> coe v1
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'fresh_20 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.just-slot
d_just'45'slot_2036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny -> AgdaAny
d_just'45'slot_2036 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_just'45'slot_2036 v1 v5
du_just'45'slot_2036 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_just'45'slot_2036 v0 v1
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v2 -> coe v1
      C_e'45'inl_14 v2 v3 -> coe v1
      C_e'45'inr_16 v2 v3 -> coe v1
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'fresh_20 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.sub-slot-sound
d_sub'45'slot'45'sound_2060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_sub'45'slot'45'sound_2060 ~v0 v1 v2 ~v3 v4 ~v5 ~v6 v7
  = du_sub'45'slot'45'sound_2060 v1 v2 v4 v7
du_sub'45'slot'45'sound_2060 ::
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_sub'45'slot'45'sound_2060 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_just'45'slot_2036 (coe v1)
             (coe
                du_sub'45'reg'45'sound_1762 (coe v0) (coe v1)
                (coe du_slot'45'just_2014 (coe v0) (coe v3)))
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
d_sub'45'slots'45'sound_2194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'slots'45'sound_2194 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.sub-any
d_sub'45'any_2208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_RegExpect_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'any_2208 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.sub-expect-sound
d_sub'45'expect'45'sound_2256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Expect_24 ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sub'45'expect'45'sound_2256 ~v0 v1 v2 v3 ~v4 v5
  = du_sub'45'expect'45'sound_2256 v1 v2 v3 v5
du_sub'45'expect'45'sound_2256 ::
  T_Expect_24 ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sub'45'expect'45'sound_2256 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_sub'45'reg'45'sound_1762 (coe d_e'45'in1_34 (coe v0))
                              (coe d_e'45'in1_34 (coe v1)) (coe v4))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_sub'45'reg'45'sound_1762 (coe d_e'45'in2_36 (coe v0))
                                 (coe d_e'45'in2_36 (coe v1)) (coe v6))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_sub'45'reg'45'sound_1762 (coe d_e'45'out_38 (coe v0))
                                    (coe d_e'45'out_38 (coe v1)) (coe v8))
                                 (coe
                                    (\ v10 ->
                                       coe
                                         du_sub'45'slot'45'sound_2060
                                         (coe
                                            d_slot'45'get_44 (coe d_e'45'slot_40 (coe v0))
                                            (coe v10))
                                         (coe
                                            d_slot'45'get_44 (coe d_e'45'slot_40 (coe v1))
                                            (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                                            (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v2))
                                            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76
                                                  (coe v2)))
                                            v10)
                                         (coe v9 v10)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.site-load-ptr
d_site'45'load'45'ptr_2284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'load'45'ptr_2284 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'load'45'ptr_2284 v1 v3 v6
du_site'45'load'45'ptr_2284 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'load'45'ptr_2284 v0 v1 v2
  = case coe v0 of
      C_e'45'repr_12 v3
        -> coe
             seq (coe v3)
             (coe
                seq (coe v2)
                (case coe v1 of
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v4
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
d_tag'45'of'45'shape_2366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'of'45'shape_2366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_tag'45'of'45'shape_2366 v7
du_tag'45'of'45'shape_2366 ::
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'of'45'shape_2366 v0
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
d_tag'45'of'45'μ_2412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'of'45'μ_2412 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_tag'45'of'45'μ_2412 v5 v9
du_tag'45'of'45'μ_2412 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'of'45'μ_2412 v0 v1
  = coe seq (coe v0) (coe du_tag'45'of'45'shape_2366 (coe v1))
-- Once.CCC.Codegen.ShapeTable.Sem.site-branch-tag
d_site'45'branch'45'tag_2432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'branch'45'tag_2432 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'branch'45'tag_2432 v1 v3 v6
du_site'45'branch'45'tag_2432 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'branch'45'tag_2432 v0 v1 v2
  = case coe v0 of
      C_e'45'repr_12 v3
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v4 v5
               -> case coe v2 of
                    C_rs'45'ptr_1180 v7 v9
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                     (coe du_tag'45'of'45'shape_2366 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v4
               -> case coe v2 of
                    C_rs'45'ptr_1180 v6 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_170 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe
                                               du_go_2508
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                  (coe v4) (coe v3))
                                               (coe
                                                  d_as'45'sum'45'of_224
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                     (coe v4) (coe v3)))
                                               (coe v16)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v4
               -> case coe v2 of
                    C_rs'45'ptr_1180 v6 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'ν_184 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe
                                               du_go_2556
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                  (coe v4) (coe v3))
                                               (coe
                                                  d_as'45'sum'45'of_224
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
d_go_2508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17
  = du_go_2508 v9 v10 v17
du_go_2508 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2508 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe seq (coe v3) (coe du_tag'45'of'45'μ_2412 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.go
d_go_2556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17
  = du_go_2556 v9 v10 v17
du_go_2556 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2556 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe seq (coe v3) (coe du_tag'45'of'45'μ_2412 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.writeHeapMem-aux
d_writeHeapMem'45'aux_2598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_writeHeapMem'45'aux_2598 ~v0 = du_writeHeapMem'45'aux_2598
du_writeHeapMem'45'aux_2598 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_writeHeapMem'45'aux_2598 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_758 v2
      v3 v4
-- Once.CCC.Codegen.ShapeTable.Sem._.writeLocToHeap
d_writeLocToHeap_2600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToHeap_2600 ~v0 = du_writeLocToHeap_2600
du_writeLocToHeap_2600 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToHeap_2600
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_784
-- Once.CCC.Codegen.ShapeTable.Sem.nothing≢just
d_nothing'8802'just_2606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_2606 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.read-uw
d_read'45'uw_2618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'uw_2618 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.go
d_go_2654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_2654 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.tag-uw
d_tag'45'uw_2668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_tag'45'uw_2668 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.shape-uw
d_shape'45'uw_2712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_shape'45'uw_2712 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_shape'45'uw_2712 v3 v9
du_shape'45'uw_2712 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
du_shape'45'uw_2712 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'unit_76
        -> coe MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'unit_76
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_98 v7 v8 v10 v11 v12 v15 v16 v17 v18 v19
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v20 v21
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_98 v7 v8 v10
                    v11 v12 v15 v16 v17 (coe du_shape'45'uw_2712 (coe v20) (coe v18))
                    (coe du_shape'45'uw_2712 (coe v21) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure_120 v3 v8 v10 v11 v12 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure_120 v3 v8
             v10 v11 v12 v15 v16 (coe du_shape'45'uw_2712 (coe v3) (coe v17))
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138 v7 v9 v10 v13 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v16 v17
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138 v7 v9 v10
                    v13 v14 (coe du_shape'45'uw_2712 (coe v16) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156 v7 v9 v10 v13 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v16 v17
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156 v7 v9 v10
                    v13 v14 (coe du_shape'45'uw_2712 (coe v17) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_170 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_170 v7
                    (coe
                       du_shape'45'uw_2712
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
                       du_shape'45'uw_2712
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
d_meets'45'cell'45'uw_2894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_meets'45'cell'45'uw_2894 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                           ~v10
  = du_meets'45'cell'45'uw_2894 v1 v8
du_meets'45'cell'45'uw_2894 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_meets'45'cell'45'uw_2894 v0 v1
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
                                                  (coe du_shape'45'uw_2712 (coe v2) (coe v10)))))
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
                                        (coe du_inl'45'uw_2948 (coe v2) (coe v9))))
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
                                        (coe du_inr'45'uw_2988 (coe v3) (coe v9))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'fresh_20 v2 v3
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.inl-uw
d_inl'45'uw_2948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_InlAt_1200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_InlAt_1200 -> T_InlAt_1200
d_inl'45'uw_2948 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16
  = du_inl'45'uw_2948 v1 v16
du_inl'45'uw_2948 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InlAt_1200 -> T_InlAt_1200
du_inl'45'uw_2948 v0 v1
  = case coe v1 of
      C_constructor_1248 v2 v3 v4 v5 v8 v9 v10
        -> coe
             C_constructor_1248 v2 v3 v4 v5 v8 v9
             (coe du_shape'45'uw_2712 (coe v0) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.inr-uw
d_inr'45'uw_2988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_InrAt_1260 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_InrAt_1260 -> T_InrAt_1260
d_inr'45'uw_2988 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16
  = du_inr'45'uw_2988 v2 v16
du_inr'45'uw_2988 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InrAt_1260 -> T_InrAt_1260
du_inr'45'uw_2988 v0 v1
  = case coe v1 of
      C_constructor_1308 v2 v3 v4 v5 v8 v9 v10
        -> coe
             C_constructor_1308 v2 v3 v4 v5 v8 v9
             (coe du_shape'45'uw_2712 (coe v0) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.fetch-at-pc
d_fetch'45'at'45'pc_3030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'pc_3030 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.fresh⇒ptr
d_fresh'8658'ptr_3046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fresh'8658'ptr_3046 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.site-store-ptr
d_site'45'store'45'ptr_3060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'store'45'ptr_3060 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'store'45'ptr_3060 v1 v3 v6
du_site'45'store'45'ptr_3060 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'store'45'ptr_3060 v0 v1 v2
  = coe du_site'45'load'45'ptr_2284 (coe v0) (coe v1) (coe v2)
