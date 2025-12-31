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
-- Once.Memory.Memory
d_Memory_6 :: ()
d_Memory_6 = erased
-- Once.Memory.readMem
d_readMem_8 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_8 v0 v1 = coe v0 v1
-- Once.Memory.writeMem
d_writeMem_14 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.Memory.≡ᵇ-refl
d_'8801''7495''45'refl_26 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_26 = erased
-- Once.Memory.mem-read-write
d_mem'45'read'45'write_36 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'read'45'write_36 = erased
-- Once.Memory._.lemma
d_lemma_48 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_48 = erased
-- Once.Memory.≡ᵇ-true→≡
d_'8801''7495''45'true'8594''8801'_58 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true'8594''8801'_58 = erased
-- Once.Memory.mem-read-other
d_mem'45'read'45'other_74 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'read'45'other_74 = erased
-- Once.Memory._.addr₂≢addr₁
d_addr'8322''8802'addr'8321'_90 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_addr'8322''8802'addr'8321'_90 = erased
-- Once.Memory._.≡ᵇ-false
d_'8801''7495''45'false_94 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'false_94 = erased
-- Once.Memory._.lemma
d_lemma_102 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_102 = erased
-- Once.Memory.AllocState
d_AllocState_108 = ()
data T_AllocState_108
  = C_alloc'45'state_118 (Integer -> Maybe Integer) Integer
-- Once.Memory.AllocState.mem
d_mem_114 :: T_AllocState_108 -> Integer -> Maybe Integer
d_mem_114 v0
  = case coe v0 of
      C_alloc'45'state_118 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.AllocState.heap-ptr
d_heap'45'ptr_116 :: T_AllocState_108 -> Integer
d_heap'45'ptr_116 v0
  = case coe v0 of
      C_alloc'45'state_118 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.init-alloc-state
d_init'45'alloc'45'state_120 :: T_AllocState_108
d_init'45'alloc'45'state_120
  = coe
      C_alloc'45'state_118
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe (1000 :: Integer))
-- Once.Memory.alloc-two-words
d_alloc'45'two'45'words_124 ::
  T_AllocState_108 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alloc'45'two'45'words_124 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_st''_142 (coe v0) (coe v1) (coe v2))
      (coe du_base_136 (coe v0))
-- Once.Memory._.base
d_base_136 :: T_AllocState_108 -> Integer -> Integer -> Integer
d_base_136 v0 ~v1 ~v2 = du_base_136 v0
du_base_136 :: T_AllocState_108 -> Integer
du_base_136 v0 = coe d_heap'45'ptr_116 (coe v0)
-- Once.Memory._.m₁
d_m'8321'_138 ::
  T_AllocState_108 -> Integer -> Integer -> Integer -> Maybe Integer
d_m'8321'_138 v0 v1 ~v2 = du_m'8321'_138 v0 v1
du_m'8321'_138 ::
  T_AllocState_108 -> Integer -> Integer -> Maybe Integer
du_m'8321'_138 v0 v1
  = coe
      d_writeMem_14 (coe d_mem_114 (coe v0)) (coe du_base_136 (coe v0))
      (coe v1)
-- Once.Memory._.m₂
d_m'8322'_140 ::
  T_AllocState_108 -> Integer -> Integer -> Integer -> Maybe Integer
d_m'8322'_140 v0 v1 v2
  = coe
      d_writeMem_14 (coe du_m'8321'_138 (coe v0) (coe v1))
      (coe addInt (coe (8 :: Integer)) (coe du_base_136 (coe v0)))
      (coe v2)
-- Once.Memory._.st'
d_st''_142 ::
  T_AllocState_108 -> Integer -> Integer -> T_AllocState_108
d_st''_142 v0 v1 v2
  = coe
      C_alloc'45'state_118 (coe d_m'8322'_140 (coe v0) (coe v1) (coe v2))
      (coe addInt (coe (16 :: Integer)) (coe du_base_136 (coe v0)))
-- Once.Memory.n≢n+suc-m
d_n'8802'n'43'suc'45'm_148 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'n'43'suc'45'm_148 = erased
-- Once.Memory._.suc-injective
d_suc'45'injective_166 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'injective_166 = erased
-- Once.Memory.n≢n+8
d_n'8802'n'43'8_170 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'n'43'8_170 = erased
-- Once.Memory.alloc-two-words-fst
d_alloc'45'two'45'words'45'fst_184 ::
  T_AllocState_108 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'two'45'words'45'fst_184 = erased
-- Once.Memory._.base
d_base_196 :: T_AllocState_108 -> Integer -> Integer -> Integer
d_base_196 v0 ~v1 ~v2 = du_base_196 v0
du_base_196 :: T_AllocState_108 -> Integer
du_base_196 v0 = coe d_heap'45'ptr_116 (coe v0)
-- Once.Memory._.m₁
d_m'8321'_198 ::
  T_AllocState_108 -> Integer -> Integer -> Integer -> Maybe Integer
d_m'8321'_198 v0 v1 ~v2 = du_m'8321'_198 v0 v1
du_m'8321'_198 ::
  T_AllocState_108 -> Integer -> Integer -> Maybe Integer
du_m'8321'_198 v0 v1
  = coe
      d_writeMem_14 (coe d_mem_114 (coe v0)) (coe du_base_196 (coe v0))
      (coe v1)
-- Once.Memory._.m₂
d_m'8322'_200 ::
  T_AllocState_108 -> Integer -> Integer -> Integer -> Maybe Integer
d_m'8322'_200 v0 v1 v2
  = coe
      d_writeMem_14 (coe du_m'8321'_198 (coe v0) (coe v1))
      (coe addInt (coe (8 :: Integer)) (coe du_base_196 (coe v0)))
      (coe v2)
-- Once.Memory._.step1
d_step1_202 ::
  T_AllocState_108 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step1_202 = erased
-- Once.Memory._.step2
d_step2_206 ::
  T_AllocState_108 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_206 = erased
-- Once.Memory.alloc-two-words-snd
d_alloc'45'two'45'words'45'snd_218 ::
  T_AllocState_108 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'two'45'words'45'snd_218 = erased
