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
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Float.Value
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
d_Layout_30 a0 a1 a2 a3 a4 a5 = ()
data T_Layout_30
  = C_l'45'unit_34 | C_l'45'int_38 | C_l'45'float_42 |
    C_l'45'pair_60 [Integer] [Integer] T_Layout_30 T_Layout_30 |
    C_l'45'inl_76 [Integer] [Integer] T_Layout_30 |
    C_l'45'inr_92 [Integer] [Integer] T_Layout_30
-- Once.Spec.ABI.PCS
d_PCS_94 a0 = ()
data T_PCS_94
  = C_sysv'45'x86'45'64_96 | C_lp64d'45'riscv64_98 |
    C_sysv'45'i386_100
-- Once.Spec.ABI.Class
d_Class_102 a0 = ()
data T_Class_102 = C_int'45'word_104 | C_float'45'word_106
-- Once.Spec.ABI.merge
d_merge_108 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_Class_102 -> T_Class_102 -> T_Class_102
d_merge_108 ~v0 v1 v2 = du_merge_108 v1 v2
du_merge_108 :: T_Class_102 -> T_Class_102 -> T_Class_102
du_merge_108 v0 v1
  = case coe v0 of
      C_int'45'word_104 -> coe v0
      C_float'45'word_106 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.merges
d_merges_110 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  [T_Class_102] -> [T_Class_102] -> [T_Class_102]
d_merges_110 ~v0 v1 v2 = du_merges_110 v1 v2
du_merges_110 :: [T_Class_102] -> [T_Class_102] -> [T_Class_102]
du_merges_110 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v1 of
             [] -> coe v0
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe du_merge_108 (coe v2) (coe v4))
                    (coe du_merges_110 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.classes
d_classes_128 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Class_102]
d_classes_128 ~v0 v1 v2 = du_classes_128 v1 v2
du_classes_128 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Class_102]
du_classes_128 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_int'45'word_104)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_float'45'word_106)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe du_classes_128 (coe v6) (coe v4))
                    (coe du_classes_128 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_int'45'word_104)
                    (coe
                       du_merges_110 (coe du_classes_128 (coe v6) (coe v4))
                       (coe du_classes_128 (coe v7) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.Loc
d_Loc_138 a0 = ()
data T_Loc_138
  = C_ireg_140 Integer | C_freg_142 Integer | C_mem_144 Integer
-- Once.Spec.ABI.by-class
d_by'45'class_146 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  [T_Class_102] -> Integer -> Integer -> [T_Loc_138]
d_by'45'class_146 ~v0 v1 v2 v3 = du_by'45'class_146 v1 v2 v3
du_by'45'class_146 ::
  [T_Class_102] -> Integer -> Integer -> [T_Loc_138]
du_by'45'class_146 v0 v1 v2
  = case coe v0 of
      [] -> coe v0
      (:) v3 v4
        -> case coe v3 of
             C_int'45'word_104
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_ireg_140 (coe v1))
                    (coe
                       du_by'45'class_146 (coe v4)
                       (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2))
             C_float'45'word_106
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_freg_142 (coe v2))
                    (coe
                       du_by'45'class_146 (coe v4) (coe v1)
                       (coe addInt (coe (1 :: Integer)) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.in-memory
d_in'45'memory_164 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer -> Integer -> [T_Loc_138]
d_in'45'memory_164 ~v0 v1 v2 = du_in'45'memory_164 v1 v2
du_in'45'memory_164 :: Integer -> Integer -> [T_Loc_138]
du_in'45'memory_164 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_mem_144 (coe v0))
                (coe
                   du_in'45'memory_164 (coe addInt (coe (1 :: Integer)) (coe v0))
                   (coe v2)))
-- Once.Spec.ABI.small?
d_small'63'_172 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] -> Integer -> Bool
d_small'63'_172 ~v0 v1 = du_small'63'_172 v1
du_small'63'_172 :: Integer -> Bool
du_small'63'_172 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
      (coe (2 :: Integer))
-- Once.Spec.ABI.scalar?
d_scalar'63'_178 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
d_scalar'63'_178 ~v0 ~v1 v2 = du_scalar'63'_178 v2
du_scalar'63'_178 :: MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
du_scalar'63'_178 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Spec.ABI.fields
d_fields_182 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Maybe [T_Class_102]
d_fields_182 ~v0 v1 v2 = du_fields_182 v1 v2
du_fields_182 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Maybe [T_Class_102]
du_fields_182 v0 v1
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
                (coe C_int'45'word_104)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_float'45'word_106)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du_zipWith_112
                    (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
                    (coe du_fields_182 (coe v6) (coe v4))
                    (coe du_fields_182 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.any-float
d_any'45'float_188 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  [T_Class_102] -> Bool
d_any'45'float_188 ~v0 v1 = du_any'45'float_188 v1
du_any'45'float_188 :: [T_Class_102] -> Bool
du_any'45'float_188 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> case coe v1 of
             C_int'45'word_104 -> coe du_any'45'float_188 (coe v2)
             C_float'45'word_106 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.fp-eligible
d_fp'45'eligible_194 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
d_fp'45'eligible_194 ~v0 v1 v2 = du_fp'45'eligible_194 v1 v2
du_fp'45'eligible_194 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
du_fp'45'eligible_194 v0 v1
  = let v2 = coe du_fields_182 (coe v0) (coe v1) in
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
                   (coe du_any'45'float_188 (coe v3))
                   (coe
                      MAlonzo.Code.Data.Bool.Base.d_not_22
                      (coe
                         eqInt (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
                         (coe (0 :: Integer)))))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Spec.ABI.answer-in-registers
d_answer'45'in'45'registers_210 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
d_answer'45'in'45'registers_210 ~v0 v1 v2 v3
  = du_answer'45'in'45'registers_210 v1 v2 v3
du_answer'45'in'45'registers_210 ::
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Bool
du_answer'45'in'45'registers_210 v0 v1 v2
  = case coe v0 of
      C_sysv'45'x86'45'64_96
        -> coe du_small'63'_172 (coe du_words_14 (coe v1) (coe v2))
      C_lp64d'45'riscv64_98
        -> coe du_small'63'_172 (coe du_words_14 (coe v1) (coe v2))
      C_sysv'45'i386_100
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_scalar'63'_178 (coe v2))
             (coe
                eqInt (coe du_words_14 (coe v1) (coe v2)) (coe (0 :: Integer)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.answer
d_answer_220 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Loc_138]
d_answer_220 ~v0 v1 v2 v3 = du_answer_220 v1 v2 v3
du_answer_220 ::
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Loc_138]
du_answer_220 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe du_answer'45'in'45'registers_210 (coe v0) (coe v1) (coe v2))
      (coe du_in'45'registers_236 (coe v1) (coe v2) (coe v0))
      (coe
         du_in'45'memory_164 (coe (0 :: Integer))
         (coe du_words_14 (coe v1) (coe v2)))
-- Once.Spec.ABI._.in-ireg
d_in'45'ireg_230 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  Integer -> Integer -> [T_Loc_138]
d_in'45'ireg_230 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_in'45'ireg_230 v4 v5
du_in'45'ireg_230 :: Integer -> Integer -> [T_Loc_138]
du_in'45'ireg_230 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_ireg_140 (coe v1))
                (coe
                   du_in'45'ireg_230 (coe v2)
                   (coe addInt (coe (1 :: Integer)) (coe v1))))
-- Once.Spec.ABI._.in-registers
d_in'45'registers_236 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> T_PCS_94 -> [T_Loc_138]
d_in'45'registers_236 ~v0 ~v1 v2 v3 v4
  = du_in'45'registers_236 v2 v3 v4
du_in'45'registers_236 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> T_PCS_94 -> [T_Loc_138]
du_in'45'registers_236 v0 v1 v2
  = case coe v2 of
      C_sysv'45'x86'45'64_96
        -> coe
             du_by'45'class_146 (coe du_classes_128 (coe v0) (coe v1))
             (coe (0 :: Integer)) (coe (0 :: Integer))
      C_lp64d'45'riscv64_98
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe du_fp'45'eligible_194 (coe v0) (coe v1))
             (coe
                du_by'45'class_146 (coe du_classes_128 (coe v0) (coe v1))
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe
                du_in'45'ireg_230 (coe du_words_14 (coe v0) (coe v1))
                (coe (0 :: Integer)))
      C_sysv'45'i386_100
        -> coe
             du_by'45'class_146 (coe du_classes_128 (coe v0) (coe v1))
             (coe (0 :: Integer)) (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.ABI.argument
d_argument_242 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Loc_138]
d_argument_242 ~v0 v1 v2 v3 v4 v5 = du_argument_242 v1 v2 v3 v4 v5
du_argument_242 ::
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> [T_Loc_138]
du_argument_242 v0 v1 v2 v3 v4
  = coe
      du_go_260 (coe v1) (coe v3) (coe v0)
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe du_answer'45'in'45'registers_210 (coe v0) (coe v2) (coe v4))
         (coe (0 :: Integer)) (coe (1 :: Integer)))
-- Once.Spec.ABI._.in-ireg
d_in'45'ireg_254 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  Integer -> Integer -> [T_Loc_138]
d_in'45'ireg_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_in'45'ireg_254 v6 v7
du_in'45'ireg_254 :: Integer -> Integer -> [T_Loc_138]
du_in'45'ireg_254 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_ireg_140 (coe v1))
                (coe
                   du_in'45'ireg_254 (coe v2)
                   (coe addInt (coe (1 :: Integer)) (coe v1))))
-- Once.Spec.ABI._.go
d_go_260 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_PCS_94 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_PCS_94 -> Integer -> [T_Loc_138]
d_go_260 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 = du_go_260 v2 v4 v6 v7
du_go_260 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_PCS_94 -> Integer -> [T_Loc_138]
du_go_260 v0 v1 v2 v3
  = case coe v2 of
      C_sysv'45'x86'45'64_96
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe du_small'63'_172 (coe du_words_14 (coe v0) (coe v1)))
             (coe
                du_by'45'class_146 (coe du_classes_128 (coe v0) (coe v1)) (coe v3)
                (coe (0 :: Integer)))
             (coe
                du_in'45'memory_164 (coe (0 :: Integer))
                (coe du_words_14 (coe v0) (coe v1)))
      C_lp64d'45'riscv64_98
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe du_fp'45'eligible_194 (coe v0) (coe v1))
             (coe
                du_by'45'class_146 (coe du_classes_128 (coe v0) (coe v1)) (coe v3)
                (coe (0 :: Integer)))
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe du_small'63'_172 (coe du_words_14 (coe v0) (coe v1)))
                (coe
                   du_in'45'ireg_254 (coe du_words_14 (coe v0) (coe v1)) (coe v3))
                (coe
                   du_in'45'memory_164 (coe (0 :: Integer))
                   (coe du_words_14 (coe v0) (coe v1))))
      C_sysv'45'i386_100
        -> coe
             du_in'45'memory_164 (coe v3) (coe du_words_14 (coe v0) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
