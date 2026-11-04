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

module MAlonzo.Code.Once.Spec.ABI where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.ABI._.⟦_⟧ᵛ
d_'10214'_'10215''7515'_10 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7515'_10 = erased
-- Once.Spec.ABI.words
d_words_14 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Integer
d_words_14 ~v0 v1 v2 = du_words_14 v1 v2
du_words_14 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Integer
du_words_14 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    addInt (coe du_words_14 (coe v6) (coe v4))
                    (coe du_words_14 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                       (coe du_words_14 (coe v6) (coe v4))
                       (coe du_words_14 (coe v7) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.Layout
d_Layout_28 a0 a1 a2 a3 a4 = ()
data T_Layout_28
  = C_l'45'unit_30 | C_l'45'int_34 | C_l'45'float_38 |
    C_l'45'pair_56 [Integer] [Integer] T_Layout_28 T_Layout_28 |
    C_l'45'inl_72 [Integer] [Integer] T_Layout_28 |
    C_l'45'inr_88 [Integer] [Integer] T_Layout_28
-- Once.Spec.ABI.PCS
d_PCS_90 a0 = ()
data T_PCS_90
  = C_sysv'45'x86'45'64_92 | C_lp64d'45'riscv64_94 |
    C_sysv'45'i386_96
-- Once.Spec.ABI.Class
d_Class_98 a0 = ()
data T_Class_98 = C_int'45'word_100 | C_float'45'word_102
-- Once.Spec.ABI.merge
d_merge_104 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_Class_98 -> T_Class_98 -> T_Class_98
d_merge_104 ~v0 v1 v2 = du_merge_104 v1 v2
du_merge_104 :: T_Class_98 -> T_Class_98 -> T_Class_98
du_merge_104 v0 v1
  = case coe v0 of
      C_int'45'word_100 -> coe v0
      C_float'45'word_102 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.merges
d_merges_106 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  [T_Class_98] -> [T_Class_98] -> [T_Class_98]
d_merges_106 ~v0 v1 v2 = du_merges_106 v1 v2
du_merges_106 :: [T_Class_98] -> [T_Class_98] -> [T_Class_98]
du_merges_106 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v1 of
             [] -> coe v0
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe du_merge_104 (coe v2) (coe v4))
                    (coe du_merges_106 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.classes
d_classes_124 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Class_98]
d_classes_124 ~v0 v1 v2 = du_classes_124 v1 v2
du_classes_124 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Class_98]
du_classes_124 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_int'45'word_100)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_float'45'word_102)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe du_classes_124 (coe v6) (coe v4))
                    (coe du_classes_124 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_int'45'word_100)
                    (coe
                       du_merges_106 (coe du_classes_124 (coe v6) (coe v4))
                       (coe du_classes_124 (coe v7) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.Loc
d_Loc_134 a0 = ()
data T_Loc_134
  = C_ireg_136 Integer | C_freg_138 Integer | C_mem_140 Integer
-- Once.Spec.ABI.by-class
d_by'45'class_142 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  [T_Class_98] -> Integer -> Integer -> [T_Loc_134]
d_by'45'class_142 ~v0 v1 v2 v3 = du_by'45'class_142 v1 v2 v3
du_by'45'class_142 ::
  [T_Class_98] -> Integer -> Integer -> [T_Loc_134]
du_by'45'class_142 v0 v1 v2
  = case coe v0 of
      [] -> coe v0
      (:) v3 v4
        -> case coe v3 of
             C_int'45'word_100
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_ireg_136 (coe v1))
                    (coe
                       du_by'45'class_142 (coe v4)
                       (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2))
             C_float'45'word_102
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_freg_138 (coe v2))
                    (coe
                       du_by'45'class_142 (coe v4) (coe v1)
                       (coe addInt (coe (1 :: Integer)) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.in-memory
d_in'45'memory_160 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer -> Integer -> [T_Loc_134]
d_in'45'memory_160 ~v0 v1 v2 = du_in'45'memory_160 v1 v2
du_in'45'memory_160 :: Integer -> Integer -> [T_Loc_134]
du_in'45'memory_160 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_mem_140 (coe v0))
                (coe
                   du_in'45'memory_160 (coe addInt (coe (1 :: Integer)) (coe v0))
                   (coe v2)))
-- Once.Spec.ABI.small?
d_small'63'_168 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] -> Integer -> Bool
d_small'63'_168 ~v0 v1 = du_small'63'_168 v1
du_small'63'_168 :: Integer -> Bool
du_small'63'_168 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
      (coe (2 :: Integer))
-- Once.Spec.ABI.scalar?
d_scalar'63'_174 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
d_scalar'63'_174 ~v0 ~v1 v2 = du_scalar'63'_174 v2
du_scalar'63'_174 :: MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
du_scalar'63'_174 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Spec.ABI.fields
d_fields_178 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Maybe [T_Class_98]
d_fields_178 ~v0 v1 v2 = du_fields_178 v1 v2
du_fields_178 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Maybe [T_Class_98]
du_fields_178 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_int'45'word_100)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_float'45'word_102)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du_zipWith_112
                    (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
                    (coe du_fields_178 (coe v6) (coe v4))
                    (coe du_fields_178 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.any-float
d_any'45'float_184 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  [T_Class_98] -> Bool
d_any'45'float_184 ~v0 v1 = du_any'45'float_184 v1
du_any'45'float_184 :: [T_Class_98] -> Bool
du_any'45'float_184 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> case coe v1 of
             C_int'45'word_100 -> coe du_any'45'float_184 (coe v2)
             C_float'45'word_102 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.fp-eligible
d_fp'45'eligible_190 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
d_fp'45'eligible_190 ~v0 v1 v2 = du_fp'45'eligible_190 v1 v2
du_fp'45'eligible_190 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
du_fp'45'eligible_190 v0 v1
  = let v2 = coe du_fields_178 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                   (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
                   (coe (2 :: Integer)))
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                   (coe du_any'45'float_184 (coe v3))
                   (coe
                      MAlonzo.Code.Data.Bool.Base.d_not_22
                      (coe
                         eqInt (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
                         (coe (0 :: Integer)))))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Spec.ABI.answer-in-registers
d_answer'45'in'45'registers_206 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
d_answer'45'in'45'registers_206 ~v0 v1 v2 v3
  = du_answer'45'in'45'registers_206 v1 v2 v3
du_answer'45'in'45'registers_206 ::
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
du_answer'45'in'45'registers_206 v0 v1 v2
  = case coe v0 of
      C_sysv'45'x86'45'64_92
        -> coe du_small'63'_168 (coe du_words_14 (coe v1) (coe v2))
      C_lp64d'45'riscv64_94
        -> coe du_small'63'_168 (coe du_words_14 (coe v1) (coe v2))
      C_sysv'45'i386_96
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_scalar'63'_174 (coe v2))
             (coe
                eqInt (coe du_words_14 (coe v1) (coe v2)) (coe (0 :: Integer)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.answer
d_answer_216 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Loc_134]
d_answer_216 ~v0 v1 v2 v3 = du_answer_216 v1 v2 v3
du_answer_216 ::
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Loc_134]
du_answer_216 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe du_answer'45'in'45'registers_206 (coe v0) (coe v1) (coe v2))
      (coe du_in'45'registers_232 (coe v1) (coe v2) (coe v0))
      (coe
         du_in'45'memory_160 (coe (0 :: Integer))
         (coe du_words_14 (coe v1) (coe v2)))
-- Once.Spec.ABI._.in-ireg
d_in'45'ireg_226 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  Integer -> Integer -> [T_Loc_134]
d_in'45'ireg_226 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_in'45'ireg_226 v4 v5
du_in'45'ireg_226 :: Integer -> Integer -> [T_Loc_134]
du_in'45'ireg_226 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_ireg_136 (coe v1))
                (coe
                   du_in'45'ireg_226 (coe v2)
                   (coe addInt (coe (1 :: Integer)) (coe v1))))
-- Once.Spec.ABI._.in-registers
d_in'45'registers_232 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> T_PCS_90 -> [T_Loc_134]
d_in'45'registers_232 ~v0 ~v1 v2 v3 v4
  = du_in'45'registers_232 v2 v3 v4
du_in'45'registers_232 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> T_PCS_90 -> [T_Loc_134]
du_in'45'registers_232 v0 v1 v2
  = case coe v2 of
      C_sysv'45'x86'45'64_92
        -> coe
             du_by'45'class_142 (coe du_classes_124 (coe v0) (coe v1))
             (coe (0 :: Integer)) (coe (0 :: Integer))
      C_lp64d'45'riscv64_94
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe du_fp'45'eligible_190 (coe v0) (coe v1))
             (coe
                du_by'45'class_142 (coe du_classes_124 (coe v0) (coe v1))
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe
                du_in'45'ireg_226 (coe du_words_14 (coe v0) (coe v1))
                (coe (0 :: Integer)))
      C_sysv'45'i386_96
        -> coe
             du_by'45'class_142 (coe du_classes_124 (coe v0) (coe v1))
             (coe (0 :: Integer)) (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.argument
d_argument_238 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Loc_134]
d_argument_238 ~v0 v1 v2 v3 v4 v5 = du_argument_238 v1 v2 v3 v4 v5
du_argument_238 ::
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Loc_134]
du_argument_238 v0 v1 v2 v3 v4
  = coe
      du_go_256 (coe v1) (coe v3) (coe v0)
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe du_answer'45'in'45'registers_206 (coe v0) (coe v2) (coe v4))
         (coe (0 :: Integer)) (coe (1 :: Integer)))
-- Once.Spec.ABI._.in-ireg
d_in'45'ireg_250 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  Integer -> Integer -> [T_Loc_134]
d_in'45'ireg_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_in'45'ireg_250 v6 v7
du_in'45'ireg_250 :: Integer -> Integer -> [T_Loc_134]
du_in'45'ireg_250 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_ireg_136 (coe v1))
                (coe
                   du_in'45'ireg_250 (coe v2)
                   (coe addInt (coe (1 :: Integer)) (coe v1))))
-- Once.Spec.ABI._.go
d_go_256 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_90 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_PCS_90 -> Integer -> [T_Loc_134]
d_go_256 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 = du_go_256 v2 v4 v6 v7
du_go_256 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_PCS_90 -> Integer -> [T_Loc_134]
du_go_256 v0 v1 v2 v3
  = case coe v2 of
      C_sysv'45'x86'45'64_92
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe du_small'63'_168 (coe du_words_14 (coe v0) (coe v1)))
             (coe
                du_by'45'class_142 (coe du_classes_124 (coe v0) (coe v1)) (coe v3)
                (coe (0 :: Integer)))
             (coe
                du_in'45'memory_160 (coe (0 :: Integer))
                (coe du_words_14 (coe v0) (coe v1)))
      C_lp64d'45'riscv64_94
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe du_fp'45'eligible_190 (coe v0) (coe v1))
             (coe
                du_by'45'class_142 (coe du_classes_124 (coe v0) (coe v1)) (coe v3)
                (coe (0 :: Integer)))
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe du_small'63'_168 (coe du_words_14 (coe v0) (coe v1)))
                (coe
                   du_in'45'ireg_250 (coe du_words_14 (coe v0) (coe v1)) (coe v3))
                (coe
                   du_in'45'memory_160 (coe (0 :: Integer))
                   (coe du_words_14 (coe v0) (coe v1))))
      C_sysv'45'i386_96
        -> coe
             du_in'45'memory_160 (coe v3) (coe du_words_14 (coe v0) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
