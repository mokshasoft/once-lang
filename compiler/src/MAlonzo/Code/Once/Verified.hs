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

module MAlonzo.Code.Once.Verified where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- Once.Verified.CorrectCompiler
d_CorrectCompiler_4 = ()
data T_CorrectCompiler_4
  = C_constructor_50 (AgdaAny -> AgdaAny)
                     (AgdaAny -> AgdaAny -> AgdaAny)
                     (AgdaAny -> AgdaAny -> Maybe AgdaAny)
-- Once.Verified.CorrectCompiler.Arch
d_Arch_28 :: T_CorrectCompiler_4 -> ()
d_Arch_28 = erased
-- Once.Verified.CorrectCompiler.Source
d_Source_30 :: T_CorrectCompiler_4 -> ()
d_Source_30 = erased
-- Once.Verified.CorrectCompiler.Bytes
d_Bytes_32 :: T_CorrectCompiler_4 -> ()
d_Bytes_32 = erased
-- Once.Verified.CorrectCompiler.Behavior
d_Behavior_34 :: T_CorrectCompiler_4 -> ()
d_Behavior_34 = erased
-- Once.Verified.CorrectCompiler.⟦_⟧
d_'10214'_'10215'_36 :: T_CorrectCompiler_4 -> AgdaAny -> AgdaAny
d_'10214'_'10215'_36 v0
  = case coe v0 of
      C_constructor_50 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CorrectCompiler.exec
d_exec_38 :: T_CorrectCompiler_4 -> AgdaAny -> AgdaAny -> AgdaAny
d_exec_38 v0
  = case coe v0 of
      C_constructor_50 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CorrectCompiler.compile
d_compile_40 ::
  T_CorrectCompiler_4 -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_compile_40 v0
  = case coe v0 of
      C_constructor_50 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CorrectCompiler.correct
d_correct_48 ::
  T_CorrectCompiler_4 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_correct_48 = erased
