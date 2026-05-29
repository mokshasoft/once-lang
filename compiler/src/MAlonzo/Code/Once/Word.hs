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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties

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
-- Once.Word.Word64._⊕_
d__'8853'__48 :: Integer -> Integer -> Integer
d__'8853'__48 = coe d__'8853'__24 (coe (64 :: Integer))
-- Once.Word.Word64._⊖_
d__'8854'__50 :: Integer -> Integer -> Integer
d__'8854'__50 = coe d__'8854'__30 (coe (64 :: Integer))
-- Once.Word.Word64._⊗_
d__'8855'__52 :: Integer -> Integer -> Integer
d__'8855'__52 = coe d__'8855'__36 (coe (64 :: Integer))
-- Once.Word.Word64.Word
d_Word_54 :: ()
d_Word_54 = erased
-- Once.Word.Word64.fromℤ
d_fromℤ_56 :: Integer -> Integer
d_fromℤ_56 = coe d_fromℤ_18 (coe (64 :: Integer))
-- Once.Word.Word64.modulus
d_modulus_58 :: Integer
d_modulus_58 = coe d_modulus_8 (coe (64 :: Integer))
-- Once.Word.Word64.modulus≢0
d_modulus'8802'0_60 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_60 = coe d_modulus'8802'0_10 (coe (64 :: Integer))
-- Once.Word.Word64.norm
d_norm_62 :: Integer -> Integer
d_norm_62 = coe d_norm_14 (coe (64 :: Integer))
-- Once.Word.Word64.⊝_
d_'8861'__64 :: Integer -> Integer
d_'8861'__64 = coe d_'8861'__42 (coe (64 :: Integer))
