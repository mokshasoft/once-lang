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

module MAlonzo.Code.Once.CCC.Memory.Memory where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant

-- Once.CCC.Memory.Memory.≡ᵇ-refl
d_'8801''7495''45'refl_10 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_10 = erased
-- Once.CCC.Memory.Memory.n≢n+suc
d_n'8802'n'43'suc_18 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'n'43'suc_18 = erased
-- Once.CCC.Memory.Memory._.suc-injective
d_suc'45'injective_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'injective_34 = erased
-- Once.CCC.Memory.Memory._.helper
d_helper_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_helper_40 = erased
-- Once.CCC.Memory.Memory.n≢n+word-size-bool
d_n'8802'n'43'word'45'size'45'bool_52 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8802'n'43'word'45'size'45'bool_52 = erased
-- Once.CCC.Memory.Memory.n+word-size≢n-bool
d_n'43'word'45'size'8802'n'45'bool_58 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'43'word'45'size'8802'n'45'bool_58 = erased
-- Once.CCC.Memory.Memory.n≢n+16-bool
d_n'8802'n'43'16'45'bool_64 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8802'n'43'16'45'bool_64 = erased
-- Once.CCC.Memory.Memory.n+16≢n-bool
d_n'43'16'8802'n'45'bool_70 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'43'16'8802'n'45'bool_70 = erased
-- Once.CCC.Memory.Memory.≡ᵇ⇒≡
d_'8801''7495''8658''8801'_78 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''8658''8801'_78 = erased
-- Once.CCC.Memory.Memory.Word
d_Word_86 :: ()
d_Word_86 = erased
-- Once.CCC.Memory.Memory.Memory
d_Memory_88 :: ()
d_Memory_88 = erased
-- Once.CCC.Memory.Memory.readMem
d_readMem_90 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_90 v0 v1 = coe v0 v1
-- Once.CCC.Memory.Memory.writeMem
d_writeMem_96 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_96 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Memory.Memory.readMem-writeMem-same
d_readMem'45'writeMem'45'same_112 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'same_112 = erased
-- Once.CCC.Memory.Memory.readMem-writeMem-diff
d_readMem'45'writeMem'45'diff_138 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'diff_138 = erased
-- Once.CCC.Memory.Memory.readMem-writeMem-diff-bool
d_readMem'45'writeMem'45'diff'45'bool_186 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'diff'45'bool_186 = erased
