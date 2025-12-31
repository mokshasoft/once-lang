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

module MAlonzo.Code.Once.Postulates where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Postulates.extensionality
d_extensionality_16
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.extensionality"
-- Once.Postulates.closure-semantics-eq
d_closure'45'semantics'45'eq_26
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.closure-semantics-eq"
-- Once.Postulates.coerceIRArrow
-- Implementation: IR is ungraded, so coercion between arrow quantities is identity
d_coerceIRArrow_40 :: AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_coerceIRArrow_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = v6
-- Once.Postulates.coerceIRArrow-preserves-eval
d_coerceIRArrow'45'preserves'45'eval_58
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.coerceIRArrow-preserves-eval"
-- Once.Postulates.Memory
d_Memory_60 :: ()
d_Memory_60 = erased
-- Once.Postulates.readMem
d_readMem_62 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_62 v0 v1 = coe v0 v1
-- Once.Postulates.encode-pair-fst
d_encode'45'pair'45'fst_78
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-pair-fst"
-- Once.Postulates.encode-pair-snd
d_encode'45'pair'45'snd_90
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-pair-snd"
-- Once.Postulates.encode-inl-tag
d_encode'45'inl'45'tag_100
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inl-tag"
-- Once.Postulates.encode-inl-val
d_encode'45'inl'45'val_110
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inl-val"
-- Once.Postulates.encode-inr-tag
d_encode'45'inr'45'tag_120
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inr-tag"
-- Once.Postulates.encode-inr-val
d_encode'45'inr'45'val_130
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inr-val"
-- Once.Postulates.encode-inl-construct
d_encode'45'inl'45'construct_142
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inl-construct"
-- Once.Postulates.encode-inr-construct
d_encode'45'inr'45'construct_154
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inr-construct"
-- Once.Postulates.encode-pair-construct
d_encode'45'pair'45'construct_168
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-pair-construct"
-- Once.Postulates.encode-closure-construct
d_encode'45'closure'45'construct_186
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-closure-construct"
-- Once.Postulates.coerceQuantity
-- Implementation: Quantity coercion is identity (allows weakening/strengthening in surface syntax)
d_coerceQuantity_200 :: AgdaAny -> AgdaAny -> AgdaAny
d_coerceQuantity_200 ~v0 v1 = v1
