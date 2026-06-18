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

module MAlonzo.Code.Once.Word where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Word.Width.modulus
d_modulus_8 :: Integer -> Integer
d_modulus_8 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
      (coe v0)
-- Once.Word.Width.modulus≢0
d_modulus'8802'0_10 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_10 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'94'n'8802'0_4470
      (coe (2 :: Integer)) (coe v0)
-- Once.Word.Width.Word
d_Word_12 :: Integer -> ()
d_Word_12 = erased
-- Once.Word.Width.norm
d_norm_14 :: Integer -> Integer -> Integer
d_norm_14 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v1)
      (coe d_modulus_8 (coe v0))
-- Once.Word.Width.fromℤ
d_fromℤ_18 :: Integer -> Integer -> Integer
d_fromℤ_18 v0 v1
  = case coe v1 of
      _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
          coe d_norm_14 (coe v0) (coe v1)
      _ -> coe
             d_norm_14 (coe v0)
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_8 (coe v0))
                (d_norm_14 (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1))))
-- Once.Word.Width._⊕_
d__'8853'__24 :: Integer -> Integer -> Integer -> Integer
d__'8853'__24 v0 v1 v2
  = coe d_norm_14 (coe v0) (coe addInt (coe v1) (coe v2))
-- Once.Word.Width._⊖_
d__'8854'__30 :: Integer -> Integer -> Integer -> Integer
d__'8854'__30 v0 v1 v2
  = coe
      d_norm_14 (coe v0)
      (coe
         addInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_8 (coe v0))
            v2)
         (coe v1))
-- Once.Word.Width._⊗_
d__'8855'__36 :: Integer -> Integer -> Integer -> Integer
d__'8855'__36 v0 v1 v2
  = coe d_norm_14 (coe v0) (coe mulInt (coe v1) (coe v2))
-- Once.Word.Width.⊝_
d_'8861'__42 :: Integer -> Integer -> Integer
d_'8861'__42 v0 v1
  = coe
      d_norm_14 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_8 (coe v0))
         v1)
-- Once.Word.Width.half
d_half_46 :: Integer -> Integer
d_half_46 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer))
-- Once.Word.Width.toℤ
d_toℤ_48 :: Integer -> Integer -> Integer
d_toℤ_48 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe ltInt (coe v1) (coe d_half_46 (coe v0))) (coe v1)
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1)
         (coe d_modulus_8 (coe v0)))
-- Once.Word.Width.intMin
d_intMin_52 :: Integer -> Integer
d_intMin_52 v0 = coe d_half_46 (coe v0)
-- Once.Word.Width.negOne
d_negOne_54 :: Integer -> Integer
d_negOne_54 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (d_modulus_8 (coe v0))
      (1 :: Integer)
-- Once.Word.Width._<ˢ_
d__'60''738'__56 :: Integer -> Integer -> Integer -> Bool
d__'60''738'__56 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'60''63'__3190
         (coe d_toℤ_48 (coe v0) (coe v1)) (coe d_toℤ_48 (coe v0) (coe v2)))
-- Once.Word.Width._≡ʷ_
d__'8801''695'__62 :: Integer -> Integer -> Integer -> Bool
d__'8801''695'__62 ~v0 v1 v2 = du__'8801''695'__62 v1 v2
du__'8801''695'__62 :: Integer -> Integer -> Bool
du__'8801''695'__62 v0 v1 = coe eqInt (coe v0) (coe v1)
-- Once.Word.Width._divℕ_
d__divℕ__68 :: Integer -> Integer -> Integer -> Integer
d__divℕ__68 ~v0 v1 v2 = du__divℕ__68 v1 v2
du__divℕ__68 :: Integer -> Integer -> Integer
du__divℕ__68 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1)
-- Once.Word.Width._modℕ_
d__modℕ__70 :: Integer -> Integer -> Integer -> Integer
d__modℕ__70 ~v0 v1 v2 = du__modℕ__70 v1 v2
du__modℕ__70 :: Integer -> Integer -> Integer
du__modℕ__70 v0 v1
  = case coe v1 of
      0 -> coe v0
      _ -> coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1)
-- Once.Word.Width.tdivℤ
d_tdivℤ_84 :: Integer -> Integer -> Integer -> Integer
d_tdivℤ_84 ~v0 v1 v2 = du_tdivℤ_84 v1 v2
du_tdivℤ_84 :: Integer -> Integer -> Integer
du_tdivℤ_84 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe
         MAlonzo.Code.Data.Sign.Base.d__'42'__14
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v1)))
      (coe
         du__divℕ__68
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Once.Word.Width.tmodℤ
d_tmodℤ_86 :: Integer -> Integer -> Integer -> Integer
d_tmodℤ_86 ~v0 v1 v2 = du_tmodℤ_86 v1 v2
du_tmodℤ_86 :: Integer -> Integer -> Integer
du_tmodℤ_86 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
      (coe
         du__modℕ__70
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Once.Word.Width._/ˢ_
d__'47''738'__96 :: Integer -> Integer -> Integer -> Integer
d__'47''738'__96 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v2) (coe (0 :: Integer)))
      (coe d_negOne_54 (coe v0))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe eqInt (coe v1) (coe d_intMin_52 (coe v0)))
            (coe eqInt (coe v2) (coe d_negOne_54 (coe v0))))
         (coe d_intMin_52 (coe v0))
         (coe
            d_fromℤ_18 (coe v0)
            (coe
               du_tdivℤ_84 (coe d_toℤ_48 (coe v0) (coe v1))
               (coe d_toℤ_48 (coe v0) (coe v2)))))
-- Once.Word.Width._%ˢ_
d__'37''738'__102 :: Integer -> Integer -> Integer -> Integer
d__'37''738'__102 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v2) (coe (0 :: Integer))) (coe v1)
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe eqInt (coe v1) (coe d_intMin_52 (coe v0)))
            (coe eqInt (coe v2) (coe d_negOne_54 (coe v0))))
         (coe (0 :: Integer))
         (coe
            d_fromℤ_18 (coe v0)
            (coe
               du_tmodℤ_86 (coe d_toℤ_48 (coe v0) (coe v1))
               (coe d_toℤ_48 (coe v0) (coe v2)))))
-- Once.Word.Word64._%ˢ_
d__'37''738'__110 :: Integer -> Integer -> Integer
d__'37''738'__110 = coe d__'37''738'__102 (coe (64 :: Integer))
-- Once.Word.Word64._/ˢ_
d__'47''738'__112 :: Integer -> Integer -> Integer
d__'47''738'__112 = coe d__'47''738'__96 (coe (64 :: Integer))
-- Once.Word.Word64._<ˢ_
d__'60''738'__114 :: Integer -> Integer -> Bool
d__'60''738'__114 = coe d__'60''738'__56 (coe (64 :: Integer))
-- Once.Word.Word64._≡ʷ_
d__'8801''695'__116 :: Integer -> Integer -> Bool
d__'8801''695'__116 = coe du__'8801''695'__62
-- Once.Word.Word64._⊕_
d__'8853'__118 :: Integer -> Integer -> Integer
d__'8853'__118 = coe d__'8853'__24 (coe (64 :: Integer))
-- Once.Word.Word64._⊖_
d__'8854'__120 :: Integer -> Integer -> Integer
d__'8854'__120 = coe d__'8854'__30 (coe (64 :: Integer))
-- Once.Word.Word64._⊗_
d__'8855'__122 :: Integer -> Integer -> Integer
d__'8855'__122 = coe d__'8855'__36 (coe (64 :: Integer))
-- Once.Word.Word64.Word
d_Word_124 :: ()
d_Word_124 = erased
-- Once.Word.Word64.fromℤ
d_fromℤ_126 :: Integer -> Integer
d_fromℤ_126 = coe d_fromℤ_18 (coe (64 :: Integer))
-- Once.Word.Word64.half
d_half_128 :: Integer
d_half_128 = coe d_half_46 (coe (64 :: Integer))
-- Once.Word.Word64.intMin
d_intMin_130 :: Integer
d_intMin_130 = coe d_intMin_52 (coe (64 :: Integer))
-- Once.Word.Word64.modulus
d_modulus_132 :: Integer
d_modulus_132 = coe d_modulus_8 (coe (64 :: Integer))
-- Once.Word.Word64.modulus≢0
d_modulus'8802'0_134 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_134
  = coe d_modulus'8802'0_10 (coe (64 :: Integer))
-- Once.Word.Word64.negOne
d_negOne_136 :: Integer
d_negOne_136 = coe d_negOne_54 (coe (64 :: Integer))
-- Once.Word.Word64.norm
d_norm_138 :: Integer -> Integer
d_norm_138 = coe d_norm_14 (coe (64 :: Integer))
-- Once.Word.Word64.toℤ
d_toℤ_140 :: Integer -> Integer
d_toℤ_140 = coe d_toℤ_48 (coe (64 :: Integer))
-- Once.Word.Word64.⊝_
d_'8861'__142 :: Integer -> Integer
d_'8861'__142 = coe d_'8861'__42 (coe (64 :: Integer))
