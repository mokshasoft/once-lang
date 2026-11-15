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

module MAlonzo.Code.Once.Spec.Theory where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Float.Arith
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Float.Value
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Word

-- Once.Spec.Theory.NumTy
d_NumTy_6 = ()
data T_NumTy_6 = C_int_8 | C_float_10
-- Once.Spec.Theory.⌜_⌝ⁿ
d_'8988'_'8989''8319'_14 ::
  Integer -> T_NumTy_6 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_'8988'_'8989''8319'_14 ~v0 v1 = du_'8988'_'8989''8319'_14 v1
du_'8988'_'8989''8319'_14 ::
  T_NumTy_6 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_'8988'_'8989''8319'_14 v0
  = case coe v0 of
      C_int_8 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_float_10 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Theory
d_Theory_16 = ()
data T_Theory_16
  = C_Neg_18 | C_Ring_20 | C_Division_22 | C_Order_24 |
    C_Equality_26 | C_Rounded_28
-- Once.Spec.Theory.Shape
d_Shape_30 = ()
data T_Shape_30 = C_unary_32 | C_binary_34 | C_compare_36
-- Once.Spec.Theory.Sym
d_Sym_38 a0 a1 = ()
data T_Sym_38
  = C_'8245'neg_40 | C_'8245''43'_42 | C_'8245''45'_44 |
    C_'8245''42'_46 | C_'8245''47'_48 | C_'8245''37'_50 |
    C_'8245''60'_52 | C_'8245''60''61'_54 | C_'8245''62'_56 |
    C_'8245''62''61'_58 | C_'8245''61''61'_60 | C_'8245''33''61'_62 |
    C_'8245''43''7496'_64 | C_'8245''45''7496'_66 |
    C_'8245''42''7496'_68 | C_'8245''47''7496'_70 |
    C_'8245''61''61''7496'_72 | C_'8245''33''61''7496'_74 |
    C_'8245''60''7496'_76 | C_'8245''60''61''7496'_78 |
    C_'8245''62''7496'_80 | C_'8245''62''61''7496'_82
-- Once.Spec.Theory.symDom
d_symDom_86 ::
  Integer ->
  T_NumTy_6 -> T_Shape_30 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_symDom_86 ~v0 v1 v2 = du_symDom_86 v1 v2
du_symDom_86 ::
  T_NumTy_6 -> T_Shape_30 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_symDom_86 v0 v1
  = case coe v1 of
      C_unary_32 -> coe du_'8988'_'8989''8319'_14 (coe v0)
      C_binary_34
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe du_'8988'_'8989''8319'_14 (coe v0))
             (coe du_'8988'_'8989''8319'_14 (coe v0))
      C_compare_36
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe du_'8988'_'8989''8319'_14 (coe v0))
             (coe du_'8988'_'8989''8319'_14 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.symCod
d_symCod_90 ::
  Integer ->
  T_NumTy_6 -> T_Shape_30 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_symCod_90 ~v0 v1 v2 = du_symCod_90 v1 v2
du_symCod_90 ::
  T_NumTy_6 -> T_Shape_30 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_symCod_90 v0 v1
  = case coe v1 of
      C_unary_32 -> coe du_'8988'_'8989''8319'_14 (coe v0)
      C_binary_34 -> coe du_'8988'_'8989''8319'_14 (coe v0)
      C_compare_36
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Has
d_Has_104 a0 a1 = ()
data T_Has_104
  = C_int'45'neg_106 | C_int'45'ring_108 | C_int'45'division_110 |
    C_int'45'order_112 | C_int'45'equality_114 | C_float'45'neg_116 |
    C_float'45'rounded_118 | C_float'45'order_120 |
    C_float'45'equality_122
-- Once.Spec.Theory.NegOps
d_NegOps_126 a0 = ()
newtype T_NegOps_126 = C_constructor_134 (AgdaAny -> AgdaAny)
-- Once.Spec.Theory.NegOps.neg
d_neg_132 :: T_NegOps_126 -> AgdaAny -> AgdaAny
d_neg_132 v0
  = case coe v0 of
      C_constructor_134 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.RingOps
d_RingOps_138 a0 = ()
data T_RingOps_138
  = C_constructor_162 AgdaAny AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- Once.Spec.Theory.RingOps.zero
d_zero_152 :: T_RingOps_138 -> AgdaAny
d_zero_152 v0
  = case coe v0 of
      C_constructor_162 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.RingOps.one
d_one_154 :: T_RingOps_138 -> AgdaAny
d_one_154 v0
  = case coe v0 of
      C_constructor_162 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.RingOps.add
d_add_156 :: T_RingOps_138 -> AgdaAny -> AgdaAny -> AgdaAny
d_add_156 v0
  = case coe v0 of
      C_constructor_162 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.RingOps.mul
d_mul_158 :: T_RingOps_138 -> AgdaAny -> AgdaAny -> AgdaAny
d_mul_158 v0
  = case coe v0 of
      C_constructor_162 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.RingOps.neg
d_neg_160 :: T_RingOps_138 -> AgdaAny -> AgdaAny
d_neg_160 v0
  = case coe v0 of
      C_constructor_162 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.DivisionOps
d_DivisionOps_166 a0 = ()
data T_DivisionOps_166
  = C_constructor_178 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
-- Once.Spec.Theory.DivisionOps.div
d_div_174 :: T_DivisionOps_166 -> AgdaAny -> AgdaAny -> AgdaAny
d_div_174 v0
  = case coe v0 of
      C_constructor_178 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.DivisionOps.mod
d_mod_176 :: T_DivisionOps_166 -> AgdaAny -> AgdaAny -> AgdaAny
d_mod_176 v0
  = case coe v0 of
      C_constructor_178 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.OrderOps
d_OrderOps_182 a0 = ()
newtype T_OrderOps_182
  = C_constructor_190 (AgdaAny -> AgdaAny -> Bool)
-- Once.Spec.Theory.OrderOps.lt
d_lt_188 :: T_OrderOps_182 -> AgdaAny -> AgdaAny -> Bool
d_lt_188 v0
  = case coe v0 of
      C_constructor_190 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.EqualityOps
d_EqualityOps_194 a0 = ()
newtype T_EqualityOps_194
  = C_constructor_202 (AgdaAny -> AgdaAny -> Bool)
-- Once.Spec.Theory.EqualityOps.eq
d_eq_200 :: T_EqualityOps_194 -> AgdaAny -> AgdaAny -> Bool
d_eq_200 v0
  = case coe v0 of
      C_constructor_202 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.RoundedOps
d_RoundedOps_206 a0 = ()
data T_RoundedOps_206
  = C_constructor_222 (AgdaAny ->
                       Maybe MAlonzo.Code.Once.Spec.Float.Arith.T_Operand_8)
                      (MAlonzo.Code.Once.Spec.Float.Arith.T_Exact_58 -> AgdaAny)
                      (AgdaAny -> AgdaAny)
-- Once.Spec.Theory.RoundedOps.embed
d_embed_216 ::
  T_RoundedOps_206 ->
  AgdaAny -> Maybe MAlonzo.Code.Once.Spec.Float.Arith.T_Operand_8
d_embed_216 v0
  = case coe v0 of
      C_constructor_222 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.RoundedOps.round
d_round_218 ::
  T_RoundedOps_206 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_Exact_58 -> AgdaAny
d_round_218 v0
  = case coe v0 of
      C_constructor_222 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.RoundedOps.neg
d_neg_220 :: T_RoundedOps_206 -> AgdaAny -> AgdaAny
d_neg_220 v0
  = case coe v0 of
      C_constructor_222 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.rounded
d_rounded_226 ::
  T_RoundedOps_206 ->
  (MAlonzo.Code.Once.Spec.Float.Arith.T_Operand_8 ->
   MAlonzo.Code.Once.Spec.Float.Arith.T_Operand_8 ->
   MAlonzo.Code.Once.Spec.Float.Arith.T_Exact_58) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_rounded_226 v0 v1 v2 v3
  = coe
      d_round_218 v0
      (coe
         MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
         (coe MAlonzo.Code.Once.Spec.Float.Arith.C_invalid_60) (coe v1)
         (coe d_embed_216 v0 v2) (coe d_embed_216 v0 v3))
-- Once.Spec.Theory.exactly
d_exactly_238 ::
  T_RoundedOps_206 ->
  (MAlonzo.Code.Once.Spec.Float.Arith.T_Operand_8 ->
   MAlonzo.Code.Once.Spec.Float.Arith.T_Operand_8 -> Bool) ->
  AgdaAny -> AgdaAny -> Bool
d_exactly_238 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1)
      (coe d_embed_216 v0 v2) (coe d_embed_216 v0 v3)
-- Once.Spec.Theory._⊑_
d__'8849'__248 a0 a1 = ()
data T__'8849'__248 = C_neg'8849'ring_250 | C_neg'8849'rounded_252
-- Once.Spec.Theory.Ops
d_Ops_254 :: T_Theory_16 -> () -> ()
d_Ops_254 = erased
-- Once.Spec.Theory.restrict
d_restrict_272 ::
  T_Theory_16 -> () -> T__'8849'__248 -> AgdaAny -> T_NegOps_126
d_restrict_272 ~v0 ~v1 v2 = du_restrict_272 v2
du_restrict_272 :: T__'8849'__248 -> AgdaAny -> T_NegOps_126
du_restrict_272 v0
  = case coe v0 of
      C_neg'8849'ring_250
        -> coe (\ v1 -> coe C_constructor_134 (coe d_neg_160 (coe v1)))
      C_neg'8849'rounded_252
        -> coe (\ v1 -> coe C_constructor_134 (coe d_neg_220 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.SymFn
d_SymFn_278 :: () -> T_Shape_30 -> ()
d_SymFn_278 = erased
-- Once.Spec.Theory.⟦_⟧ₛ
d_'10214'_'10215''8347'_292 ::
  T_Theory_16 ->
  T_Shape_30 -> () -> T_Sym_38 -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214'_'10215''8347'_292 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'10214'_'10215''8347'_292 v3 v4 v5
du_'10214'_'10215''8347'_292 ::
  T_Sym_38 -> AgdaAny -> AgdaAny -> AgdaAny
du_'10214'_'10215''8347'_292 v0 v1 v2
  = case coe v0 of
      C_'8245'neg_40 -> coe d_neg_132 v1 v2
      C_'8245''43'_42
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe d_add_156 v1 v3 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''45'_44
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe d_add_156 v1 v3 (coe d_neg_160 v1 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''42'_46
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe d_mul_158 v1 v3 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''47'_48
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe d_div_174 v1 v3 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''37'_50
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe d_mod_176 v1 v3 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''60'_52
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe d_lt_188 v1 v3 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''60''61'_54
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe d_lt_188 v1 v4 v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''62'_56
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe d_lt_188 v1 v4 v3
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''62''61'_58
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe d_lt_188 v1 v3 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''61''61'_60
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe d_eq_200 v1 v3 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''33''61'_62
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe d_eq_200 v1 v3 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''43''7496'_64
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    d_round_218 v1
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.C_invalid_60)
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.d_addE_188)
                       (coe d_embed_216 v1 v3) (coe d_embed_216 v1 v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''45''7496'_66
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    d_round_218 v1
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.C_invalid_60)
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.d_addE_188)
                       (coe d_embed_216 v1 v3) (coe d_embed_216 v1 (coe d_neg_220 v1 v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''42''7496'_68
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    d_round_218 v1
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.C_invalid_60)
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.d_mulE_216)
                       (coe d_embed_216 v1 v3) (coe d_embed_216 v1 v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''47''7496'_70
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    d_round_218 v1
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.C_invalid_60)
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.d_divE_272)
                       (coe d_embed_216 v1 v3) (coe d_embed_216 v1 v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''61''61''7496'_72
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Once.Spec.Float.Arith.d_eqR_380)
                    (coe d_embed_216 v1 v3) (coe d_embed_216 v1 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''33''61''7496'_74
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d_not_22
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.d_eqR_380)
                       (coe d_embed_216 v1 v3) (coe d_embed_216 v1 v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''60''7496'_76
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Once.Spec.Float.Arith.d_ltR_344)
                    (coe d_embed_216 v1 v3) (coe d_embed_216 v1 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''60''61''7496'_78
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.d_ltR_344)
                       (coe d_embed_216 v1 v3) (coe d_embed_216 v1 v4))
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.d_eqR_380)
                       (coe d_embed_216 v1 v3) (coe d_embed_216 v1 v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''62''7496'_80
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Once.Spec.Float.Arith.d_ltR_344)
                    (coe d_embed_216 v1 v4) (coe d_embed_216 v1 v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'8245''62''61''7496'_82
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.d_ltR_344)
                       (coe d_embed_216 v1 v4) (coe d_embed_216 v1 v3))
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Arith.du_both_28
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Once.Spec.Float.Arith.d_eqR_380)
                       (coe d_embed_216 v1 v4) (coe d_embed_216 v1 v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Models.F
d_F_484 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
d_F_484 v0
  = coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0)
-- Once.Spec.Theory.Models.Val
d_Val_486 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> T_NumTy_6 -> ()
d_Val_486 = erased
-- Once.Spec.Theory.Models.Valid
d_Valid_490 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_NumTy_6 -> AgdaAny -> ()
d_Valid_490 = erased
-- Once.Spec.Theory.Models.intRing
d_intRing_496 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> T_RingOps_138
d_intRing_496 v0
  = coe
      C_constructor_162 (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.Spec.Word.d_norm_18
         (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
         (coe (1 :: Integer)))
      (coe
         MAlonzo.Code.Once.Spec.Word.d__'8853'__28
         (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)))
      (coe
         MAlonzo.Code.Once.Spec.Word.d__'8855'__40
         (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)))
      (coe
         MAlonzo.Code.Once.Spec.Word.d_'8861'__46
         (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)))
-- Once.Spec.Theory.Models.floatRounded
d_floatRounded_498 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> T_RoundedOps_206
d_floatRounded_498 v0
  = coe
      C_constructor_222
      (coe MAlonzo.Code.Once.Spec.Float.Arith.d_exact_14)
      (coe
         MAlonzo.Code.Once.Spec.Float.Arith.d_round_66
         (coe d_F_484 (coe v0)))
      (coe MAlonzo.Code.Once.Spec.Float.Value.d_negV_38)
-- Once.Spec.Theory.Models.structure
d_structure_504 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_NumTy_6 -> T_Theory_16 -> T_Has_104 -> AgdaAny
d_structure_504 v0 ~v1 ~v2 v3 = du_structure_504 v0 v3
du_structure_504 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Has_104 -> AgdaAny
du_structure_504 v0 v1
  = case coe v1 of
      C_int'45'neg_106
        -> coe
             du_restrict_272 (coe C_neg'8849'ring_250) (d_intRing_496 (coe v0))
      C_int'45'ring_108 -> coe d_intRing_496 (coe v0)
      C_int'45'division_110
        -> coe
             C_constructor_178
             (coe
                MAlonzo.Code.Once.Spec.Word.d__'47''738'__116
                (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)))
             (coe
                MAlonzo.Code.Once.Spec.Word.d__'37''738'__122
                (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)))
      C_int'45'order_112
        -> coe
             C_constructor_190
             (coe
                MAlonzo.Code.Once.Spec.Word.d__'60''738'__76
                (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)))
      C_int'45'equality_114
        -> coe
             C_constructor_202
             (coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82)
      C_float'45'neg_116
        -> coe
             du_restrict_272 (coe C_neg'8849'rounded_252)
             (d_floatRounded_498 (coe v0))
      C_float'45'rounded_118 -> coe d_floatRounded_498 (coe v0)
      C_float'45'order_120
        -> coe
             C_constructor_190
             (coe MAlonzo.Code.Once.Spec.Float.Arith.d_ltT_390)
      C_float'45'equality_122
        -> coe
             C_constructor_202
             (coe MAlonzo.Code.Once.Spec.Float.Arith.d_eqV_396)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Laws.NegLaws
d_NegLaws_514 a0 a1 a2 = ()
newtype T_NegLaws_514
  = C_constructor_542 (AgdaAny -> AgdaAny -> AgdaAny)
-- Once.Spec.Theory.Laws._.neg
d_neg_520 :: T_NegOps_126 -> AgdaAny -> AgdaAny
d_neg_520 v0 = coe d_neg_132 (coe v0)
-- Once.Spec.Theory.Laws.NegLaws._.neg
d_neg_532 ::
  () ->
  (AgdaAny -> ()) ->
  T_NegOps_126 -> T_NegLaws_514 -> AgdaAny -> AgdaAny
d_neg_532 ~v0 ~v1 v2 ~v3 = du_neg_532 v2
du_neg_532 :: T_NegOps_126 -> AgdaAny -> AgdaAny
du_neg_532 v0 = coe d_neg_132 (coe v0)
-- Once.Spec.Theory.Laws.NegLaws.neg-closed
d_neg'45'closed_536 ::
  T_NegLaws_514 -> AgdaAny -> AgdaAny -> AgdaAny
d_neg'45'closed_536 v0
  = case coe v0 of
      C_constructor_542 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Laws.NegLaws.involutive
d_involutive_540 ::
  T_NegLaws_514 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_involutive_540 = erased
-- Once.Spec.Theory.Laws.RingLaws
d_RingLaws_546 a0 a1 a2 = ()
data T_RingLaws_546
  = C_constructor_706 (AgdaAny ->
                       AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Once.Spec.Theory.Laws._.add
d_add_552 :: T_RingOps_138 -> AgdaAny -> AgdaAny -> AgdaAny
d_add_552 v0 = coe d_add_156 (coe v0)
-- Once.Spec.Theory.Laws._.mul
d_mul_554 :: T_RingOps_138 -> AgdaAny -> AgdaAny -> AgdaAny
d_mul_554 v0 = coe d_mul_158 (coe v0)
-- Once.Spec.Theory.Laws._.neg
d_neg_556 :: T_RingOps_138 -> AgdaAny -> AgdaAny
d_neg_556 v0 = coe d_neg_160 (coe v0)
-- Once.Spec.Theory.Laws._.one
d_one_558 :: T_RingOps_138 -> AgdaAny
d_one_558 v0 = coe d_one_154 (coe v0)
-- Once.Spec.Theory.Laws._.zero
d_zero_560 :: T_RingOps_138 -> AgdaAny
d_zero_560 v0 = coe d_zero_152 (coe v0)
-- Once.Spec.Theory.Laws.RingLaws._.add
d_add_630 ::
  () ->
  (AgdaAny -> ()) ->
  T_RingOps_138 -> T_RingLaws_546 -> AgdaAny -> AgdaAny -> AgdaAny
d_add_630 ~v0 ~v1 v2 ~v3 = du_add_630 v2
du_add_630 :: T_RingOps_138 -> AgdaAny -> AgdaAny -> AgdaAny
du_add_630 v0 = coe d_add_156 (coe v0)
-- Once.Spec.Theory.Laws.RingLaws._.mul
d_mul_632 ::
  () ->
  (AgdaAny -> ()) ->
  T_RingOps_138 -> T_RingLaws_546 -> AgdaAny -> AgdaAny -> AgdaAny
d_mul_632 ~v0 ~v1 v2 ~v3 = du_mul_632 v2
du_mul_632 :: T_RingOps_138 -> AgdaAny -> AgdaAny -> AgdaAny
du_mul_632 v0 = coe d_mul_158 (coe v0)
-- Once.Spec.Theory.Laws.RingLaws._.neg
d_neg_634 ::
  () ->
  (AgdaAny -> ()) ->
  T_RingOps_138 -> T_RingLaws_546 -> AgdaAny -> AgdaAny
d_neg_634 ~v0 ~v1 v2 ~v3 = du_neg_634 v2
du_neg_634 :: T_RingOps_138 -> AgdaAny -> AgdaAny
du_neg_634 v0 = coe d_neg_160 (coe v0)
-- Once.Spec.Theory.Laws.RingLaws._.one
d_one_636 ::
  () -> (AgdaAny -> ()) -> T_RingOps_138 -> T_RingLaws_546 -> AgdaAny
d_one_636 ~v0 ~v1 v2 ~v3 = du_one_636 v2
du_one_636 :: T_RingOps_138 -> AgdaAny
du_one_636 v0 = coe d_one_154 (coe v0)
-- Once.Spec.Theory.Laws.RingLaws._.zero
d_zero_638 ::
  () -> (AgdaAny -> ()) -> T_RingOps_138 -> T_RingLaws_546 -> AgdaAny
d_zero_638 ~v0 ~v1 v2 ~v3 = du_zero_638 v2
du_zero_638 :: T_RingOps_138 -> AgdaAny
du_zero_638 v0 = coe d_zero_152 (coe v0)
-- Once.Spec.Theory.Laws.RingLaws.add-closed
d_add'45'closed_644 ::
  T_RingLaws_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_add'45'closed_644 v0
  = case coe v0 of
      C_constructor_706 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Laws.RingLaws.mul-closed
d_mul'45'closed_650 ::
  T_RingLaws_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mul'45'closed_650 v0
  = case coe v0 of
      C_constructor_706 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Laws.RingLaws.+-assoc
d_'43''45'assoc_658 ::
  T_RingLaws_546 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_658 = erased
-- Once.Spec.Theory.Laws.RingLaws.+-comm
d_'43''45'comm_664 ::
  T_RingLaws_546 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_664 = erased
-- Once.Spec.Theory.Laws.RingLaws.+-identityˡ
d_'43''45'identity'737'_668 ::
  T_RingLaws_546 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737'_668 = erased
-- Once.Spec.Theory.Laws.RingLaws.+-inverseʳ
d_'43''45'inverse'691'_672 ::
  T_RingLaws_546 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'691'_672 = erased
-- Once.Spec.Theory.Laws.RingLaws.*-assoc
d_'42''45'assoc_680 ::
  T_RingLaws_546 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_680 = erased
-- Once.Spec.Theory.Laws.RingLaws.*-comm
d_'42''45'comm_686 ::
  T_RingLaws_546 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_686 = erased
-- Once.Spec.Theory.Laws.RingLaws.*-identityˡ
d_'42''45'identity'737'_690 ::
  T_RingLaws_546 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_690 = erased
-- Once.Spec.Theory.Laws.RingLaws.distribˡ
d_distrib'737'_698 ::
  T_RingLaws_546 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_698 = erased
-- Once.Spec.Theory.Laws.RingLaws.neg-mul
d_neg'45'mul_704 ::
  T_RingLaws_546 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'mul_704 = erased
-- Once.Spec.Theory.Laws.OrderLaws
d_OrderLaws_710 a0 a1 a2 = ()
data T_OrderLaws_710
  = C_constructor_758 (AgdaAny ->
                       AgdaAny ->
                       AgdaAny ->
                       AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny ->
                       AgdaAny ->
                       AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Once.Spec.Theory.Laws._.lt
d_lt_716 :: T_OrderOps_182 -> AgdaAny -> AgdaAny -> Bool
d_lt_716 v0 = coe d_lt_188 (coe v0)
-- Once.Spec.Theory.Laws.OrderLaws._.lt
d_lt_738 ::
  () ->
  (AgdaAny -> ()) ->
  T_OrderOps_182 -> T_OrderLaws_710 -> AgdaAny -> AgdaAny -> Bool
d_lt_738 ~v0 ~v1 v2 ~v3 = du_lt_738 v2
du_lt_738 :: T_OrderOps_182 -> AgdaAny -> AgdaAny -> Bool
du_lt_738 v0 = coe d_lt_188 (coe v0)
-- Once.Spec.Theory.Laws.OrderLaws.irrefl
d_irrefl_742 ::
  T_OrderLaws_710 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_742 = erased
-- Once.Spec.Theory.Laws.OrderLaws.trans
d_trans_750 ::
  T_OrderLaws_710 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_750 v0
  = case coe v0 of
      C_constructor_758 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Laws.OrderLaws.total
d_total_756 ::
  T_OrderLaws_710 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_756 v0
  = case coe v0 of
      C_constructor_758 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Laws.EqualityLaws
d_EqualityLaws_762 a0 a1 a2 = ()
newtype T_EqualityLaws_762
  = C_constructor_794 (AgdaAny -> AgdaAny -> AgdaAny)
-- Once.Spec.Theory.Laws._.eq
d_eq_768 :: T_EqualityOps_194 -> AgdaAny -> AgdaAny -> Bool
d_eq_768 v0 = coe d_eq_200 (coe v0)
-- Once.Spec.Theory.Laws.EqualityLaws._.eq
d_eq_782 ::
  () ->
  (AgdaAny -> ()) ->
  T_EqualityOps_194 ->
  T_EqualityLaws_762 -> AgdaAny -> AgdaAny -> Bool
d_eq_782 ~v0 ~v1 v2 ~v3 = du_eq_782 v2
du_eq_782 :: T_EqualityOps_194 -> AgdaAny -> AgdaAny -> Bool
du_eq_782 v0 = coe d_eq_200 (coe v0)
-- Once.Spec.Theory.Laws.EqualityLaws.sound
d_sound_788 ::
  T_EqualityLaws_762 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sound_788 = erased
-- Once.Spec.Theory.Laws.EqualityLaws.complete
d_complete_792 ::
  T_EqualityLaws_762 -> AgdaAny -> AgdaAny -> AgdaAny
d_complete_792 v0
  = case coe v0 of
      C_constructor_794 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Laws.RoundedLaws
d_RoundedLaws_798 a0 a1 a2 = ()
data T_RoundedLaws_798
  = C_constructor_858 (MAlonzo.Code.Once.Spec.Float.Arith.T_Exact_58 ->
                       AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
-- Once.Spec.Theory.Laws._.embed
d_embed_804 ::
  T_RoundedOps_206 ->
  AgdaAny -> Maybe MAlonzo.Code.Once.Spec.Float.Arith.T_Operand_8
d_embed_804 v0 = coe d_embed_216 (coe v0)
-- Once.Spec.Theory.Laws._.neg
d_neg_806 :: T_RoundedOps_206 -> AgdaAny -> AgdaAny
d_neg_806 v0 = coe d_neg_220 (coe v0)
-- Once.Spec.Theory.Laws._.round
d_round_808 ::
  T_RoundedOps_206 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_Exact_58 -> AgdaAny
d_round_808 v0 = coe d_round_218 (coe v0)
-- Once.Spec.Theory.Laws.RoundedLaws._.embed
d_embed_832 ::
  () ->
  (AgdaAny -> ()) ->
  T_RoundedOps_206 ->
  T_RoundedLaws_798 ->
  AgdaAny -> Maybe MAlonzo.Code.Once.Spec.Float.Arith.T_Operand_8
d_embed_832 ~v0 ~v1 v2 ~v3 = du_embed_832 v2
du_embed_832 ::
  T_RoundedOps_206 ->
  AgdaAny -> Maybe MAlonzo.Code.Once.Spec.Float.Arith.T_Operand_8
du_embed_832 v0 = coe d_embed_216 (coe v0)
-- Once.Spec.Theory.Laws.RoundedLaws._.neg
d_neg_834 ::
  () ->
  (AgdaAny -> ()) ->
  T_RoundedOps_206 -> T_RoundedLaws_798 -> AgdaAny -> AgdaAny
d_neg_834 ~v0 ~v1 v2 ~v3 = du_neg_834 v2
du_neg_834 :: T_RoundedOps_206 -> AgdaAny -> AgdaAny
du_neg_834 v0 = coe d_neg_220 (coe v0)
-- Once.Spec.Theory.Laws.RoundedLaws._.round
d_round_836 ::
  () ->
  (AgdaAny -> ()) ->
  T_RoundedOps_206 ->
  T_RoundedLaws_798 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_Exact_58 -> AgdaAny
d_round_836 ~v0 ~v1 v2 ~v3 = du_round_836 v2
du_round_836 ::
  T_RoundedOps_206 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_Exact_58 -> AgdaAny
du_round_836 v0 = coe d_round_218 (coe v0)
-- Once.Spec.Theory.Laws.RoundedLaws.round-closed
d_round'45'closed_840 ::
  T_RoundedLaws_798 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_Exact_58 -> AgdaAny
d_round'45'closed_840 v0
  = case coe v0 of
      C_constructor_858 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Laws.RoundedLaws.retract
d_retract_844 ::
  T_RoundedLaws_798 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_retract_844 = erased
-- Once.Spec.Theory.Laws.RoundedLaws.neg-closed
d_neg'45'closed_848 ::
  T_RoundedLaws_798 -> AgdaAny -> AgdaAny -> AgdaAny
d_neg'45'closed_848 v0
  = case coe v0 of
      C_constructor_858 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Theory.Laws.RoundedLaws.neg-exact
d_neg'45'exact_852 ::
  T_RoundedLaws_798 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'exact_852 = erased
-- Once.Spec.Theory.Laws.RoundedLaws.round-odd
d_round'45'odd_856 ::
  T_RoundedLaws_798 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_Exact_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'odd_856 = erased
-- Once.Spec.Theory.Laws.Laws
d_Laws_862 :: () -> (AgdaAny -> ()) -> T_Theory_16 -> AgdaAny -> ()
d_Laws_862 = erased
