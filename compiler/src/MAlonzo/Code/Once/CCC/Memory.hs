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

module MAlonzo.Code.Once.CCC.Memory where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant

-- Once.CCC.Memory.≡ᵇ-refl
d_'8801''7495''45'refl_8 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_8 = erased
-- Once.CCC.Memory.n≢n+suc
d_n'8802'n'43'suc_16 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'n'43'suc_16 = erased
-- Once.CCC.Memory._.suc-injective
d_suc'45'injective_32 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'injective_32 = erased
-- Once.CCC.Memory._.helper
d_helper_38 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_helper_38 = erased
-- Once.CCC.Memory.n≢n+word-size-bool
d_n'8802'n'43'word'45'size'45'bool_50 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8802'n'43'word'45'size'45'bool_50 = erased
-- Once.CCC.Memory.n+word-size≢n-bool
d_n'43'word'45'size'8802'n'45'bool_56 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'43'word'45'size'8802'n'45'bool_56 = erased
-- Once.CCC.Memory.n≢n+16-bool
d_n'8802'n'43'16'45'bool_62 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8802'n'43'16'45'bool_62 = erased
-- Once.CCC.Memory.n+16≢n-bool
d_n'43'16'8802'n'45'bool_68 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'43'16'8802'n'45'bool_68 = erased
-- Once.CCC.Memory.≡ᵇ⇒≡
d_'8801''7495''8658''8801'_76 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''8658''8801'_76 = erased
-- Once.CCC.Memory.Word
d_Word_84 :: ()
d_Word_84 = erased
-- Once.CCC.Memory.Memory
d_Memory_86 :: ()
d_Memory_86 = erased
-- Once.CCC.Memory.readMem
d_readMem_88 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_88 v0 v1 = coe v0 v1
-- Once.CCC.Memory.writeMem
d_writeMem_94 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_94 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Memory.readMem-writeMem-same
d_readMem'45'writeMem'45'same_110 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'same_110 = erased
-- Once.CCC.Memory.readMem-writeMem-diff
d_readMem'45'writeMem'45'diff_136 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'diff_136 = erased
-- Once.CCC.Memory.readMem-writeMem-diff-bool
d_readMem'45'writeMem'45'diff'45'bool_184 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'diff'45'bool_184 = erased
