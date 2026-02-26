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
-- Once.Postulates.Memory
d_Memory_28 :: ()
d_Memory_28 = erased
-- Once.Postulates.readMem
d_readMem_30 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_30 v0 v1 = coe v0 v1
-- Once.Postulates.encode-pair-fst
d_encode'45'pair'45'fst_46
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-pair-fst"
-- Once.Postulates.encode-pair-snd
d_encode'45'pair'45'snd_58
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-pair-snd"
-- Once.Postulates.encode-inl-tag
d_encode'45'inl'45'tag_68
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inl-tag"
-- Once.Postulates.encode-inl-val
d_encode'45'inl'45'val_78
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inl-val"
-- Once.Postulates.encode-inr-tag
d_encode'45'inr'45'tag_88
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inr-tag"
-- Once.Postulates.encode-inr-val
d_encode'45'inr'45'val_98
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inr-val"
-- Once.Postulates.encode-inl-construct
d_encode'45'inl'45'construct_110
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inl-construct"
-- Once.Postulates.encode-inr-construct
d_encode'45'inr'45'construct_122
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inr-construct"
-- Once.Postulates.encode-pair-construct
d_encode'45'pair'45'construct_136
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-pair-construct"
-- Once.Postulates.encode-closure-env
d_encode'45'closure'45'env_146
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-closure-env"
-- Once.Postulates.encode-closure-construct
d_encode'45'closure'45'construct_164
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-closure-construct"
-- Once.Postulates.coerceQuantity
d_coerceQuantity_178
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.coerceQuantity"
