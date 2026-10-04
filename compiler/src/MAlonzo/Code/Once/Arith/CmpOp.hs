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

module MAlonzo.Code.Once.Arith.CmpOp where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.CmpOp.CmpOp
d_CmpOp_6 = ()
data T_CmpOp_6
  = C_c'45'lt_8 | C_c'45'le_10 | C_c'45'gt_12 | C_c'45'ge_14 |
    C_c'45'eq_16 | C_c'45'ne_18
-- Once.Arith.CmpOp.cmp-word
d_cmp'45'word_22 ::
  Integer -> T_CmpOp_6 -> Integer -> Integer -> Bool
d_cmp'45'word_22 v0 v1 v2 v3
  = case coe v1 of
      C_c'45'lt_8
        -> coe
             MAlonzo.Code.Once.Word.d__'60''738'__80 (coe v0) (coe v2) (coe v3)
      C_c'45'le_10
        -> coe
             MAlonzo.Code.Data.Bool.Base.d_not_22
             (coe
                MAlonzo.Code.Once.Word.d__'60''738'__80 (coe v0) (coe v3) (coe v2))
      C_c'45'gt_12
        -> coe
             MAlonzo.Code.Once.Word.d__'60''738'__80 (coe v0) (coe v3) (coe v2)
      C_c'45'ge_14
        -> coe
             MAlonzo.Code.Data.Bool.Base.d_not_22
             (coe
                MAlonzo.Code.Once.Word.d__'60''738'__80 (coe v0) (coe v2) (coe v3))
      C_c'45'eq_16
        -> coe MAlonzo.Code.Once.Word.du__'8801''695'__86 (coe v2) (coe v3)
      C_c'45'ne_18
        -> coe
             MAlonzo.Code.Data.Bool.Base.d_not_22
             (coe MAlonzo.Code.Once.Word.du__'8801''695'__86 (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.CmpOp.cmp-bit
d_cmp'45'bit_62 ::
  Integer -> T_CmpOp_6 -> Integer -> Integer -> Integer
d_cmp'45'bit_62 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_cmp'45'word_22 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe (1 :: Integer)) (coe (0 :: Integer))
