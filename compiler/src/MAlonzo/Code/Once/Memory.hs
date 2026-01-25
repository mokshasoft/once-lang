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

module MAlonzo.Code.Once.Memory where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant

-- Once.Memory.Word
d_Word_4 :: ()
d_Word_4 = erased
-- Once.Memory.word-size
d_word'45'size_6 :: Integer
d_word'45'size_6 = coe (8 :: Integer)
-- Once.Memory.two-words
d_two'45'words_8 :: Integer
d_two'45'words_8
  = coe addInt (coe d_word'45'size_6) (coe d_word'45'size_6)
-- Once.Memory.Memory
d_Memory_10 :: ()
d_Memory_10 = erased
-- Once.Memory.readMem
d_readMem_12 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_12 v0 v1 = coe v0 v1
-- Once.Memory.writeMem
d_writeMem_18 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.Memory.≡ᵇ-refl
d_'8801''7495''45'refl_30 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_30 = erased
-- Once.Memory.mem-read-write
d_mem'45'read'45'write_40 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'read'45'write_40 = erased
-- Once.Memory._.lemma
d_lemma_52 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_52 = erased
-- Once.Memory.≡ᵇ-true→≡
d_'8801''7495''45'true'8594''8801'_62 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true'8594''8801'_62 = erased
-- Once.Memory.mem-read-other
d_mem'45'read'45'other_78 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'read'45'other_78 = erased
-- Once.Memory._.addr₂≢addr₁
d_addr'8322''8802'addr'8321'_94 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_addr'8322''8802'addr'8321'_94 = erased
-- Once.Memory._.≡ᵇ-false
d_'8801''7495''45'false_98 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'false_98 = erased
-- Once.Memory._.lemma
d_lemma_106 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_106 = erased
-- Once.Memory.AllocState
d_AllocState_112 = ()
data T_AllocState_112
  = C_alloc'45'state_122 (Integer -> Maybe Integer) Integer
-- Once.Memory.AllocState.mem
d_mem_118 :: T_AllocState_112 -> Integer -> Maybe Integer
d_mem_118 v0
  = case coe v0 of
      C_alloc'45'state_122 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.AllocState.heap-ptr
d_heap'45'ptr_120 :: T_AllocState_112 -> Integer
d_heap'45'ptr_120 v0
  = case coe v0 of
      C_alloc'45'state_122 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.init-alloc-state
d_init'45'alloc'45'state_124 :: T_AllocState_112
d_init'45'alloc'45'state_124
  = coe
      C_alloc'45'state_122
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe (1000 :: Integer))
-- Once.Memory.alloc-two-words
d_alloc'45'two'45'words_128 ::
  T_AllocState_112 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alloc'45'two'45'words_128 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_st''_146 (coe v0) (coe v1) (coe v2))
      (coe du_base_140 (coe v0))
-- Once.Memory._.base
d_base_140 :: T_AllocState_112 -> Integer -> Integer -> Integer
d_base_140 v0 ~v1 ~v2 = du_base_140 v0
du_base_140 :: T_AllocState_112 -> Integer
du_base_140 v0 = coe d_heap'45'ptr_120 (coe v0)
-- Once.Memory._.m₁
d_m'8321'_142 ::
  T_AllocState_112 -> Integer -> Integer -> Integer -> Maybe Integer
d_m'8321'_142 v0 v1 ~v2 = du_m'8321'_142 v0 v1
du_m'8321'_142 ::
  T_AllocState_112 -> Integer -> Integer -> Maybe Integer
du_m'8321'_142 v0 v1
  = coe
      d_writeMem_18 (coe d_mem_118 (coe v0)) (coe du_base_140 (coe v0))
      (coe v1)
-- Once.Memory._.m₂
d_m'8322'_144 ::
  T_AllocState_112 -> Integer -> Integer -> Integer -> Maybe Integer
d_m'8322'_144 v0 v1 v2
  = coe
      d_writeMem_18 (coe du_m'8321'_142 (coe v0) (coe v1))
      (coe addInt (coe du_base_140 (coe v0)) (coe d_word'45'size_6))
      (coe v2)
-- Once.Memory._.st'
d_st''_146 ::
  T_AllocState_112 -> Integer -> Integer -> T_AllocState_112
d_st''_146 v0 v1 v2
  = coe
      C_alloc'45'state_122 (coe d_m'8322'_144 (coe v0) (coe v1) (coe v2))
      (coe addInt (coe du_base_140 (coe v0)) (coe d_two'45'words_8))
-- Once.Memory.n≢n+suc-m
d_n'8802'n'43'suc'45'm_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'n'43'suc'45'm_152 = erased
-- Once.Memory._.suc-injective
d_suc'45'injective_170 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'injective_170 = erased
-- Once.Memory.n≢n+word-size
d_n'8802'n'43'word'45'size_174 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'n'43'word'45'size_174 = erased
-- Once.Memory.alloc-two-words-fst
d_alloc'45'two'45'words'45'fst_188 ::
  T_AllocState_112 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'two'45'words'45'fst_188 = erased
-- Once.Memory._.base
d_base_200 :: T_AllocState_112 -> Integer -> Integer -> Integer
d_base_200 v0 ~v1 ~v2 = du_base_200 v0
du_base_200 :: T_AllocState_112 -> Integer
du_base_200 v0 = coe d_heap'45'ptr_120 (coe v0)
-- Once.Memory._.m₁
d_m'8321'_202 ::
  T_AllocState_112 -> Integer -> Integer -> Integer -> Maybe Integer
d_m'8321'_202 v0 v1 ~v2 = du_m'8321'_202 v0 v1
du_m'8321'_202 ::
  T_AllocState_112 -> Integer -> Integer -> Maybe Integer
du_m'8321'_202 v0 v1
  = coe
      d_writeMem_18 (coe d_mem_118 (coe v0)) (coe du_base_200 (coe v0))
      (coe v1)
-- Once.Memory._.m₂
d_m'8322'_204 ::
  T_AllocState_112 -> Integer -> Integer -> Integer -> Maybe Integer
d_m'8322'_204 v0 v1 v2
  = coe
      d_writeMem_18 (coe du_m'8321'_202 (coe v0) (coe v1))
      (coe addInt (coe du_base_200 (coe v0)) (coe d_word'45'size_6))
      (coe v2)
-- Once.Memory._.step1
d_step1_206 ::
  T_AllocState_112 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step1_206 = erased
-- Once.Memory._.step2
d_step2_210 ::
  T_AllocState_112 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_210 = erased
-- Once.Memory.alloc-two-words-snd
d_alloc'45'two'45'words'45'snd_222 ::
  T_AllocState_112 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'two'45'words'45'snd_222 = erased
