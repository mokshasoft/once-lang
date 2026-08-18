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

module MAlonzo.Code.Once.Semantics.FloatBits where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Float.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base

-- Once.Semantics.FloatBits.float-bits
d_float'45'bits_6 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 -> Integer
d_float'45'bits_6 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44 word64ToNat
      (0 :: Integer) (coe MAlonzo.Code.Data.Float.Base.d_toWord_14 v0)
-- Once.Semantics.FloatBits.2^23
d_2'94'23_10 :: Integer
d_2'94'23_10 = coe (8388608 :: Integer)
-- Once.Semantics.FloatBits.2^29
d_2'94'29_12 :: Integer
d_2'94'29_12 = coe (536870912 :: Integer)
-- Once.Semantics.FloatBits.2^31
d_2'94'31_14 :: Integer
d_2'94'31_14 = coe (2147483648 :: Integer)
-- Once.Semantics.FloatBits.2^52
d_2'94'52_16 :: Integer
d_2'94'52_16 = coe (4503599627370496 :: Integer)
-- Once.Semantics.FloatBits.2^63
d_2'94'63_18 :: Integer
d_2'94'63_18 = coe (9223372036854775808 :: Integer)
-- Once.Semantics.FloatBits.2^11
d_2'94'11_20 :: Integer
d_2'94'11_20 = coe (2048 :: Integer)
-- Once.Semantics.FloatBits.float-bits-single
d_float'45'bits'45'single_22 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 -> Integer
d_float'45'bits'45'single_22 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         eqInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'37'__330
            (coe
               MAlonzo.Code.Data.Nat.Base.du__'47'__318
               (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'52_16))
            (coe d_2'94'11_20))
         (coe (0 :: Integer)))
      (coe
         mulInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318
            (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'63_18))
         (coe d_2'94'31_14))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            eqInt
            (coe
               MAlonzo.Code.Data.Nat.Base.du__'37'__330
               (coe
                  MAlonzo.Code.Data.Nat.Base.du__'47'__318
                  (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'52_16))
               (coe d_2'94'11_20))
            (coe (2047 :: Integer)))
         (coe
            addInt
            (coe
               addInt
               (coe
                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                  (coe
                     eqInt
                     (coe
                        MAlonzo.Code.Data.Nat.Base.du__'37'__330
                        (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'52_16))
                     (coe (0 :: Integer)))
                  (coe (0 :: Integer)) (coe (1 :: Integer)))
               (coe mulInt (coe (255 :: Integer)) (coe d_2'94'23_10)))
            (coe
               mulInt
               (coe
                  MAlonzo.Code.Data.Nat.Base.du__'47'__318
                  (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'63_18))
               (coe d_2'94'31_14)))
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               ltInt
               (coe
                  MAlonzo.Code.Data.Nat.Base.du__'37'__330
                  (coe
                     MAlonzo.Code.Data.Nat.Base.du__'47'__318
                     (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'52_16))
                  (coe d_2'94'11_20))
               (coe (897 :: Integer)))
            (coe
               mulInt
               (coe
                  MAlonzo.Code.Data.Nat.Base.du__'47'__318
                  (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'63_18))
               (coe d_2'94'31_14))
            (coe
               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
               (coe
                  ltInt (coe (1150 :: Integer))
                  (coe
                     MAlonzo.Code.Data.Nat.Base.du__'37'__330
                     (coe
                        MAlonzo.Code.Data.Nat.Base.du__'47'__318
                        (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'52_16))
                     (coe d_2'94'11_20)))
               (coe
                  addInt (coe mulInt (coe (255 :: Integer)) (coe d_2'94'23_10))
                  (coe
                     mulInt
                     (coe
                        MAlonzo.Code.Data.Nat.Base.du__'47'__318
                        (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'63_18))
                     (coe d_2'94'31_14)))
               (coe
                  addInt
                  (coe
                     addInt
                     (coe
                        MAlonzo.Code.Data.Nat.Base.du__'47'__318
                        (coe
                           MAlonzo.Code.Data.Nat.Base.du__'37'__330
                           (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'52_16))
                        (coe d_2'94'29_12))
                     (coe
                        mulInt
                        (coe
                           MAlonzo.Code.Data.Nat.Base.du__'47'__318
                           (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'63_18))
                        (coe d_2'94'31_14)))
                  (coe
                     mulInt
                     (coe
                        MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                        (addInt
                           (coe (127 :: Integer))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.du__'37'__330
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.du__'47'__318
                                 (coe d_float'45'bits_6 (coe v0)) (coe d_2'94'52_16))
                              (coe d_2'94'11_20)))
                        (1023 :: Integer))
                     (coe d_2'94'23_10))))))
