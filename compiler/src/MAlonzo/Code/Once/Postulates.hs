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
-- Type-level coercion: IR Γ (A ⇒[q₁] B) → IR Γ (A ⇒[q₂] B)
-- Identity at runtime since IR representation doesn't depend on quantity annotation
d_coerceIRArrow_38 v0 v1 v2 v3 v4 v5 = coe v5
-- Once.Postulates.coerceIRArrow-preserves-eval
d_coerceIRArrow'45'preserves'45'eval_54
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.coerceIRArrow-preserves-eval"
-- Once.Postulates.Memory
d_Memory_56 :: ()
d_Memory_56 = erased
-- Once.Postulates.readMem
d_readMem_58 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_58 v0 v1 = coe v0 v1
-- Once.Postulates.encode-pair-fst
d_encode'45'pair'45'fst_74
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-pair-fst"
-- Once.Postulates.encode-pair-snd
d_encode'45'pair'45'snd_86
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-pair-snd"
-- Once.Postulates.encode-inl-tag
d_encode'45'inl'45'tag_96
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inl-tag"
-- Once.Postulates.encode-inl-val
d_encode'45'inl'45'val_106
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inl-val"
-- Once.Postulates.encode-inr-tag
d_encode'45'inr'45'tag_116
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inr-tag"
-- Once.Postulates.encode-inr-val
d_encode'45'inr'45'val_126
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inr-val"
-- Once.Postulates.encode-inl-construct
d_encode'45'inl'45'construct_138
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inl-construct"
-- Once.Postulates.encode-inr-construct
d_encode'45'inr'45'construct_150
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-inr-construct"
-- Once.Postulates.encode-pair-construct
d_encode'45'pair'45'construct_164
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-pair-construct"
-- Once.Postulates.encode-closure-env
d_encode'45'closure'45'env_174
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-closure-env"
-- Once.Postulates.encode-closure-code-ptr
d_encode'45'closure'45'code'45'ptr_184
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-closure-code-ptr"
-- Once.Postulates.encode-closure-construct
d_encode'45'closure'45'construct_200
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.encode-closure-construct"
-- Once.Postulates.coerceQuantity
d_coerceQuantity_214
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.coerceQuantity"
