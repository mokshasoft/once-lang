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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_Expect_24
d_step'45'expect_318 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             C_mkExpect_42 (coe d_e'45'out_38 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2244
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'out_38 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2246
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'in2_36 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1))
             (coe d_load'45'fst_284 (coe d_e'45'in1_34 (coe v1)))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1))
             (coe d_load'45'snd_300 (coe d_e'45'in1_34 (coe v1)))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2252 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1))
             (coe d_slot'45'get_44 (coe d_e'45'slot_40 (coe v1)) (coe v3))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2254 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe
                d_slot'45'put_76 (coe d_e'45'slot_40 (coe v1)) (coe v3)
                (coe d_e'45'out_38 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2260 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2262 v3
        -> coe
             C_mkExpect_42
             (coe d_slot'45'get_44 (coe d_e'45'slot_40 (coe v1)) (coe v3))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2264 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2266 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2268 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2270 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2272
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2274
        -> coe
             C_mkExpect_42 (coe C_e'45'any_10) (coe C_e'45'any_10)
             (coe C_e'45'any_10)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2276 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2278 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe d_e'45'out_38 (coe v1))
             (coe
                d_slot'45'put_76 (coe d_e'45'slot_40 (coe v1)) (coe v3)
                (coe d_e'45'out_38 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2280 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1))
             (coe d_slot'45'get_44 (coe d_e'45'slot_40 (coe v1)) (coe v3))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2282 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v3 v4 v5
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2292 v3 v4 v5
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2294 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'any_10)
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2296
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2298 v3
        -> coe
             C_mkExpect_42 (coe d_e'45'in1_34 (coe v1))
             (coe d_e'45'in2_36 (coe v1)) (coe C_e'45'tag_18 (coe v3))
             (coe d_e'45'slot_40 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2300 v3 v4
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2302 v3
        -> coe
             C_mkExpect_42
             (coe d_e'45'in1_34 (coe du_scrub'45'expect_522 (coe v1)))
             (coe d_e'45'in2_36 (coe du_scrub'45'expect_522 (coe v1)))
             (coe
                C_e'45'fresh_20 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
             (coe d_e'45'slot_40 (coe du_scrub'45'expect_522 (coe v1)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2304 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2306 v3
        -> coe v1
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2230 v4
               -> coe v0 v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2232 v4
               -> coe
                    C_mkExpect_42 (coe C_e'45'any_10) (coe C_e'45'any_10)
                    (coe C_e'45'any_10)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2234 v4
               -> coe v1
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2236 v4
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
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2310 v3
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
d_is'45'fresh_616 :: T_RegExpect_8 -> Bool
d_is'45'fresh_616 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_e'45'fresh_20 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Codegen.ShapeTable.is-just
d_is'45'just_620 :: () -> Maybe AgdaAny -> Bool
d_is'45'just_620 ~v0 v1 = du_is'45'just_620 v1
du_is'45'just_620 :: Maybe AgdaAny -> Bool
du_is'45'just_620 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.tag-site-ok
d_tag'45'site'45'ok_622 :: T_RegExpect_8 -> Bool
d_tag'45'site'45'ok_622 v0
  = let v1 = coe du_is'45'just_620 (coe d_as'45'sum_242 (coe v0)) in
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
d_site'45'ok_630 ::
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> Bool
d_site'45'ok_630 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2248
           -> coe d_is'45'ptr_252 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2250
           -> coe d_is'45'ptr_252 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2256
           -> coe d_is'45'fresh_616 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2258
           -> coe d_is'45'fresh_616 (coe d_e'45'in1_34 (coe v0))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2236 v4
                  -> coe d_tag'45'site'45'ok_622 (coe d_e'45'in1_34 (coe v0))
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Codegen.ShapeTable.ctrl-ok
d_ctrl'45'ok_646 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> Bool
d_ctrl'45'ok_646 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v4
           -> case coe v4 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2230 v5
                  -> coe d_sub'45'expect_218 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2232 v5
                  -> coe d_sub'45'expect_218 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2234 v5
                  -> coe d_sub'45'expect_218 (coe v1) (coe v0 v5)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2236 v5
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
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
-- Once.CCC.Codegen.ShapeTable.check-shapes
d_check'45'shapes_740 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> Bool
d_check'45'shapes_740 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_site'45'ok_630 (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe d_ctrl'45'ok_646 (coe v0) (coe v1) (coe v3))
                (coe
                   d_check'45'shapes_740 (coe v0)
                   (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v3)) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.scan-expect
d_scan'45'expect_754 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [T_Expect_24]
d_scan'45'expect_754 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe
                d_scan'45'expect_754 (coe v0)
                (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v3)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.scan-length
d_scan'45'length_774 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scan'45'length_774 = erased
-- Once.CCC.Codegen.ShapeTable.post-expect
d_post'45'expect_792 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_Expect_24
d_post'45'expect_792 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4
        -> coe
             d_post'45'expect_792 (coe v0)
             (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v3)) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.check-++
d_check'45''43''43'_814 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_check'45''43''43'_814 = erased
-- Once.CCC.Codegen.ShapeTable._.∧-assoc₂
d_'8743''45'assoc'8322'_844 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Bool ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc'8322'_844 = erased
-- Once.CCC.Codegen.ShapeTable.post-++
d_post'45''43''43'_872 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_post'45''43''43'_872 = erased
-- Once.CCC.Codegen.ShapeTable.IsHeap
d_IsHeap_890 :: MAlonzo.Code.Once.IR.T_AllocMode_4 -> ()
d_IsHeap_890 = erased
-- Once.CCC.Codegen.ShapeTable.HeapModed
d_HeapModed_896 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_HeapModed_896 = erased
-- Once.CCC.Codegen.ShapeTable.entry-expect
d_entry'45'expect_934 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_Expect_24
d_entry'45'expect_934 v0
  = coe
      C_mkExpect_42 (coe C_e'45'repr_12 (coe v0)) (coe C_e'45'any_10)
      (coe C_e'45'any_10)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Codegen.ShapeTable.at-pc
d_at'45'pc_938 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_at'45'pc_938 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_at'45'pc_938 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.state-at
d_state'45'at_952 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> T_Expect_24
d_state'45'at_952 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe v1
      (:) v4 v5
        -> case coe v3 of
             0 -> coe v1
             _ -> let v6 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       d_state'45'at_952 (coe v0)
                       (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.∧-split
d_'8743''45'split_982 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_982 v0 v1 ~v2 = du_'8743''45'split_982 v0 v1
du_'8743''45'split_982 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_982 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.CCC.Codegen.ShapeTable.check-at
d_check'45'at_996 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'at_996 v0 v1 v2 v3 ~v4 ~v5 ~v6
  = du_check'45'at_996 v0 v1 v2 v3
du_check'45'at_996 ::
  (Integer -> T_Expect_24) ->
  T_Expect_24 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'at_996 v0 v1 v2 v3
  = case coe v2 of
      (:) v4 v5
        -> case coe v3 of
             0 -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_'8743''45'split_982 (coe d_site'45'ok_630 (coe v1) (coe v4))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                             (coe d_ctrl'45'ok_646 (coe v0) (coe v1) (coe v4))
                             (coe
                                d_check'45'shapes_740 (coe v0)
                                (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v4)) (coe v5)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_'8743''45'split_982
                          (coe d_ctrl'45'ok_646 (coe v0) (coe v1) (coe v4))
                          (coe
                             d_check'45'shapes_740 (coe v0)
                             (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v4)) (coe v5))))
             _ -> let v6 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_check'45'at_996 (coe v0)
                       (coe d_step'45'expect_318 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.readLoc
d_readLoc_1036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_1036 ~v0 = du_readLoc_1036
du_readLoc_1036 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_1036
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState
d_FlatState_1040 a0 = ()
-- Once.CCC.Codegen.ShapeTable.Sem._.fetch
d_fetch_1046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_fetch_1046 ~v0 = du_fetch_1046
du_fetch_1046 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
du_fetch_1046 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_148
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.falloc
d_falloc_1054 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_falloc_1054 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.floc
d_floc_1056 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_floc_1056 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.FlatState.fpc
d_fpc_1058 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_1058 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v0)
-- Once.CCC.Codegen.ShapeTable.Sem._.ShapeAt
d_ShapeAt_1062 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.ShapeTable.Sem._.TagAt
d_TagAt_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_TagAt_1064 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.BeforeFrontier
d_BeforeFrontier_1116 a0 a1 a2 = ()
-- Once.CCC.Codegen.ShapeTable.Sem.RegShape
d_RegShape_1132 a0 a1 a2 a3 a4 = ()
data T_RegShape_1132
  = C_rs'45'unit_1140 |
    C_rs'45'ptr_1148 MAlonzo.Code.Once.IR.T_AllocMode_4
                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 |
    C_rs'45'int_1152 | C_rs'45'float_1156
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt
d_InlAt_1168 a0 a1 a2 a3 a4 a5 = ()
data T_InlAt_1168
  = C_constructor_1216 MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-m
d_i'45'm_1198 :: T_InlAt_1168 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_i'45'm_1198 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-mA
d_i'45'mA_1200 ::
  T_InlAt_1168 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_i'45'mA_1200 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-payload
d_i'45'payload_1202 ::
  T_InlAt_1168 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_i'45'payload_1202 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-mode
d_i'45'mode_1204 :: T_InlAt_1168 -> AgdaAny
d_i'45'mode_1204 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-tag
d_i'45'tag_1206 :: T_InlAt_1168 -> AgdaAny
d_i'45'tag_1206 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-cell
d_i'45'cell_1208 ::
  T_InlAt_1168 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'45'cell_1208 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-bf-p
d_i'45'bf'45'p_1210 ::
  T_InlAt_1168 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_i'45'bf'45'p_1210 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-bf-s
d_i'45'bf'45's_1212 ::
  T_InlAt_1168 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_i'45'bf'45's_1212 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InlAt.i-pay
d_i'45'pay_1214 ::
  T_InlAt_1168 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_i'45'pay_1214 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt
d_InrAt_1228 a0 a1 a2 a3 a4 a5 = ()
data T_InrAt_1228
  = C_constructor_1276 MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-m
d_r'45'm_1258 :: T_InrAt_1228 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_r'45'm_1258 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-mB
d_r'45'mB_1260 ::
  T_InrAt_1228 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_r'45'mB_1260 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-payload
d_r'45'payload_1262 ::
  T_InrAt_1228 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_r'45'payload_1262 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-mode
d_r'45'mode_1264 :: T_InrAt_1228 -> AgdaAny
d_r'45'mode_1264 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-tag
d_r'45'tag_1266 :: T_InrAt_1228 -> AgdaAny
d_r'45'tag_1266 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-cell
d_r'45'cell_1268 ::
  T_InrAt_1228 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r'45'cell_1268 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-bf-p
d_r'45'bf'45'p_1270 ::
  T_InrAt_1228 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_r'45'bf'45'p_1270 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-bf-s
d_r'45'bf'45's_1272 ::
  T_InrAt_1228 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_r'45'bf'45's_1272 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.InrAt.r-pay
d_r'45'pay_1274 ::
  T_InrAt_1228 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_r'45'pay_1274 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsR
d_MeetsR_1278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 -> ()
d_MeetsR_1278 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsCell
d_MeetsCell_1280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 -> ()
d_MeetsCell_1280 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MCell
d_MCell_1282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 -> ()
d_MCell_1282 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.FreshAt
d_FreshAt_1284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_RegExpect_8 ->
  Maybe T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 -> ()
d_FreshAt_1284 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.MeetsSlot
d_MeetsSlot_1428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 -> ()
d_MeetsSlot_1428 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.Meets
d_Meets_1518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_Meets_1518 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.func-eq-sound
d_func'45'eq'45'sound_1530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_func'45'eq'45'sound_1530 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.ty-eq-sound
d_ty'45'eq'45'sound_1536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ty'45'eq'45'sound_1536 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.nat-eq-sound
d_nat'45'eq'45'sound_1674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'eq'45'sound_1674 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.inl-shape
d_inl'45'shape_1700 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_InlAt_1168 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_inl'45'shape_1700 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_inl'45'shape_1700 v5
du_inl'45'shape_1700 ::
  T_InlAt_1168 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
du_inl'45'shape_1700 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138
      (d_i'45'payload_1202 (coe v0)) (d_i'45'mA_1200 (coe v0))
      (d_i'45'mode_1204 (coe v0)) (d_i'45'bf'45'p_1210 (coe v0))
      (d_i'45'bf'45's_1212 (coe v0)) (d_i'45'pay_1214 (coe v0))
-- Once.CCC.Codegen.ShapeTable.Sem.inr-shape
d_inr'45'shape_1716 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_InrAt_1228 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_inr'45'shape_1716 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_inr'45'shape_1716 v5
du_inr'45'shape_1716 ::
  T_InrAt_1228 -> MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
du_inr'45'shape_1716 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156
      (d_r'45'payload_1262 (coe v0)) (d_r'45'mB_1260 (coe v0))
      (d_r'45'mode_1264 (coe v0)) (d_r'45'bf'45'p_1270 (coe v0))
      (d_r'45'bf'45's_1272 (coe v0)) (d_r'45'pay_1274 (coe v0))
-- Once.CCC.Codegen.ShapeTable.Sem.sub-reg-sound
d_sub'45'reg'45'sound_1730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_sub'45'reg'45'sound_1730 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_sub'45'reg'45'sound_1730 v1 v2 v7
du_sub'45'reg'45'sound_1730 ::
  T_RegExpect_8 -> T_RegExpect_8 -> AgdaAny -> AgdaAny
du_sub'45'reg'45'sound_1730 v0 v1 v2
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
                                  C_rs'45'ptr_1148 (d_i'45'm_1198 (coe v9))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138
                                     (d_i'45'payload_1202 (coe v9)) (d_i'45'mA_1200 (coe v9))
                                     (d_i'45'mode_1204 (coe v9)) (d_i'45'bf'45'p_1210 (coe v9))
                                     (d_i'45'bf'45's_1212 (coe v9)) (d_i'45'pay_1214 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_e'45'inr_16 v4 v5
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> coe
                                  C_rs'45'ptr_1148 (d_r'45'm_1258 (coe v9))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156
                                     (d_r'45'payload_1262 (coe v9)) (d_r'45'mB_1260 (coe v9))
                                     (d_r'45'mode_1264 (coe v9)) (d_r'45'bf'45'p_1270 (coe v9))
                                     (d_r'45'bf'45's_1272 (coe v9)) (d_r'45'pay_1274 (coe v9)))
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
                                                                                                                                          C_rs'45'ptr_1148
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
                                                                                                                     C_rs'45'ptr_1148
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
                                                                                                                     C_rs'45'ptr_1148
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
d_slot'45'just_1982 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny -> AgdaAny
d_slot'45'just_1982 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_slot'45'just_1982 v1 v5
du_slot'45'just_1982 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_slot'45'just_1982 v0 v1
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v2 -> coe v1
      C_e'45'inl_14 v2 v3 -> coe v1
      C_e'45'inr_16 v2 v3 -> coe v1
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'fresh_20 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.just-slot
d_just'45'slot_2004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny -> AgdaAny
d_just'45'slot_2004 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_just'45'slot_2004 v1 v5
du_just'45'slot_2004 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_just'45'slot_2004 v0 v1
  = case coe v0 of
      C_e'45'any_10 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_e'45'repr_12 v2 -> coe v1
      C_e'45'inl_14 v2 v3 -> coe v1
      C_e'45'inr_16 v2 v3 -> coe v1
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'fresh_20 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.sub-slot-sound
d_sub'45'slot'45'sound_2028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_sub'45'slot'45'sound_2028 ~v0 v1 v2 ~v3 v4 ~v5 ~v6 v7
  = du_sub'45'slot'45'sound_2028 v1 v2 v4 v7
du_sub'45'slot'45'sound_2028 ::
  T_RegExpect_8 ->
  T_RegExpect_8 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> AgdaAny
du_sub'45'slot'45'sound_2028 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_just'45'slot_2004 (coe v1)
             (coe
                du_sub'45'reg'45'sound_1730 (coe v0) (coe v1)
                (coe du_slot'45'just_1982 (coe v0) (coe v3)))
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
d_sub'45'slots'45'sound_2162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'slots'45'sound_2162 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.sub-any
d_sub'45'any_2176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  T_RegExpect_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'any_2176 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.sub-expect-sound
d_sub'45'expect'45'sound_2224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Expect_24 ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sub'45'expect'45'sound_2224 ~v0 v1 v2 v3 ~v4 v5
  = du_sub'45'expect'45'sound_2224 v1 v2 v3 v5
du_sub'45'expect'45'sound_2224 ::
  T_Expect_24 ->
  T_Expect_24 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sub'45'expect'45'sound_2224 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_sub'45'reg'45'sound_1730 (coe d_e'45'in1_34 (coe v0))
                              (coe d_e'45'in1_34 (coe v1)) (coe v4))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_sub'45'reg'45'sound_1730 (coe d_e'45'in2_36 (coe v0))
                                 (coe d_e'45'in2_36 (coe v1)) (coe v6))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_sub'45'reg'45'sound_1730 (coe d_e'45'out_38 (coe v0))
                                    (coe d_e'45'out_38 (coe v1)) (coe v8))
                                 (coe
                                    (\ v10 ->
                                       coe
                                         du_sub'45'slot'45'sound_2028
                                         (coe
                                            d_slot'45'get_44 (coe d_e'45'slot_40 (coe v0))
                                            (coe v10))
                                         (coe
                                            d_slot'45'get_44 (coe d_e'45'slot_40 (coe v1))
                                            (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_554
                                            (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v2))
                                            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72
                                                  (coe v2)))
                                            v10)
                                         (coe v9 v10)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.site-load-ptr
d_site'45'load'45'ptr_2252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'load'45'ptr_2252 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'load'45'ptr_2252 v1 v3 v6
du_site'45'load'45'ptr_2252 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'load'45'ptr_2252 v0 v1 v2
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
d_tag'45'of'45'shape_2334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'of'45'shape_2334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_tag'45'of'45'shape_2334 v7
du_tag'45'of'45'shape_2334 ::
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'of'45'shape_2334 v0
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
d_tag'45'of'45'μ_2380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'of'45'μ_2380 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_tag'45'of'45'μ_2380 v5 v9
du_tag'45'of'45'μ_2380 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'of'45'μ_2380 v0 v1
  = coe seq (coe v0) (coe du_tag'45'of'45'shape_2334 (coe v1))
-- Once.CCC.Codegen.ShapeTable.Sem.site-branch-tag
d_site'45'branch'45'tag_2400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'branch'45'tag_2400 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'branch'45'tag_2400 v1 v3 v6
du_site'45'branch'45'tag_2400 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'branch'45'tag_2400 v0 v1 v2
  = case coe v0 of
      C_e'45'repr_12 v3
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v4 v5
               -> case coe v2 of
                    C_rs'45'ptr_1148 v7 v9
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                     (coe du_tag'45'of'45'shape_2334 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v4
               -> case coe v2 of
                    C_rs'45'ptr_1148 v6 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_170 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe
                                               du_go_2476
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
                    C_rs'45'ptr_1148 v6 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'ν_184 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe
                                               du_go_2524
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
d_go_2476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17
  = du_go_2476 v9 v10 v17
du_go_2476 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2476 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe seq (coe v3) (coe du_tag'45'of'45'μ_2380 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.go
d_go_2524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17
  = du_go_2524 v9 v10 v17
du_go_2524 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2524 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe seq (coe v3) (coe du_tag'45'of'45'μ_2380 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.writeHeapMem-aux
d_writeHeapMem'45'aux_2566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_writeHeapMem'45'aux_2566 ~v0 = du_writeHeapMem'45'aux_2566
du_writeHeapMem'45'aux_2566 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_writeHeapMem'45'aux_2566 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_812 v2
      v3 v4
-- Once.CCC.Codegen.ShapeTable.Sem._.writeLocToHeap
d_writeLocToHeap_2568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_writeLocToHeap_2568 ~v0 = du_writeLocToHeap_2568
du_writeLocToHeap_2568 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_writeLocToHeap_2568
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_838
-- Once.CCC.Codegen.ShapeTable.Sem.nothing≢just
d_nothing'8802'just_2574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_2574 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.read-uw
d_read'45'uw_2586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'uw_2586 = erased
-- Once.CCC.Codegen.ShapeTable.Sem._.go
d_go_2622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_2622 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.tag-uw
d_tag'45'uw_2636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_tag'45'uw_2636 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.shape-uw
d_shape'45'uw_2680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
d_shape'45'uw_2680 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_shape'45'uw_2680 v3 v9
du_shape'45'uw_2680 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66 ->
  MAlonzo.Code.Once.CCC.Machine.ShapeAt.T_ShapeAt_66
du_shape'45'uw_2680 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'unit_76
        -> coe MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'unit_76
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_98 v7 v8 v10 v11 v12 v15 v16 v17 v18 v19
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v20 v21
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'pair_98 v7 v8 v10
                    v11 v12 v15 v16 v17 (coe du_shape'45'uw_2680 (coe v20) (coe v18))
                    (coe du_shape'45'uw_2680 (coe v21) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure_120 v3 v8 v10 v11 v12 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'closure_120 v3 v8
             v10 v11 v12 v15 v16 (coe du_shape'45'uw_2680 (coe v3) (coe v17))
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138 v7 v9 v10 v13 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v16 v17
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inl_138 v7 v9 v10
                    v13 v14 (coe du_shape'45'uw_2680 (coe v16) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156 v7 v9 v10 v13 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v16 v17
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'inr_156 v7 v9 v10
                    v13 v14 (coe du_shape'45'uw_2680 (coe v17) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_170 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ShapeAt.C_shape'45'μ_170 v7
                    (coe
                       du_shape'45'uw_2680
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
                       du_shape'45'uw_2680
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
d_meets'45'cell'45'uw_2862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_meets'45'cell'45'uw_2862 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                           ~v10
  = du_meets'45'cell'45'uw_2862 v1 v8
du_meets'45'cell'45'uw_2862 :: T_RegExpect_8 -> AgdaAny -> AgdaAny
du_meets'45'cell'45'uw_2862 v0 v1
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
                                                  (coe du_shape'45'uw_2680 (coe v2) (coe v10)))))
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
                                        (coe du_inl'45'uw_2916 (coe v2) (coe v9))))
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
                                        (coe du_inr'45'uw_2956 (coe v3) (coe v9))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_e'45'tag_18 v2 -> coe v1
      C_e'45'fresh_20 v2 v3
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.inl-uw
d_inl'45'uw_2916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_InlAt_1168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_InlAt_1168 -> T_InlAt_1168
d_inl'45'uw_2916 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16
  = du_inl'45'uw_2916 v1 v16
du_inl'45'uw_2916 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InlAt_1168 -> T_InlAt_1168
du_inl'45'uw_2916 v0 v1
  = case coe v1 of
      C_constructor_1216 v2 v3 v4 v5 v8 v9 v10
        -> coe
             C_constructor_1216 v2 v3 v4 v5 v8 v9
             (coe du_shape'45'uw_2680 (coe v0) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem._.inr-uw
d_inr'45'uw_2956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_InrAt_1228 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  T_InrAt_1228 -> T_InrAt_1228
d_inr'45'uw_2956 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16
  = du_inr'45'uw_2956 v2 v16
du_inr'45'uw_2956 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InrAt_1228 -> T_InrAt_1228
du_inr'45'uw_2956 v0 v1
  = case coe v1 of
      C_constructor_1276 v2 v3 v4 v5 v8 v9 v10
        -> coe
             C_constructor_1276 v2 v3 v4 v5 v8 v9
             (coe du_shape'45'uw_2680 (coe v0) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ShapeTable.Sem.fetch-at-pc
d_fetch'45'at'45'pc_2998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'pc_2998 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.fresh⇒ptr
d_fresh'8658'ptr_3014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fresh'8658'ptr_3014 = erased
-- Once.CCC.Codegen.ShapeTable.Sem.site-store-ptr
d_site'45'store'45'ptr_3028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_site'45'store'45'ptr_3028 ~v0 v1 ~v2 v3 ~v4 ~v5 v6
  = du_site'45'store'45'ptr_3028 v1 v3 v6
du_site'45'store'45'ptr_3028 ::
  T_RegExpect_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_site'45'store'45'ptr_3028 v0 v1 v2
  = coe du_site'45'load'45'ptr_2252 (coe v0) (coe v1) (coe v2)
