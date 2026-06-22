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

module MAlonzo.Code.Once.Adequacy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise

-- Once.Adequacy.CorrectCompiler
d_CorrectCompiler_4 = ()
data T_CorrectCompiler_4
  = C_constructor_54 (AgdaAny -> Maybe AgdaAny)
                     (AgdaAny -> AgdaAny -> AgdaAny)
                     (AgdaAny -> Bool -> AgdaAny -> Maybe AgdaAny)
                     (AgdaAny ->
                      Bool ->
                      AgdaAny ->
                      MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22)
-- Once.Adequacy.CorrectCompiler.Arch
d_Arch_30 :: T_CorrectCompiler_4 -> ()
d_Arch_30 = erased
-- Once.Adequacy.CorrectCompiler.Source
d_Source_32 :: T_CorrectCompiler_4 -> ()
d_Source_32 = erased
-- Once.Adequacy.CorrectCompiler.Bytes
d_Bytes_34 :: T_CorrectCompiler_4 -> ()
d_Bytes_34 = erased
-- Once.Adequacy.CorrectCompiler.Behavior
d_Behavior_36 :: T_CorrectCompiler_4 -> ()
d_Behavior_36 = erased
-- Once.Adequacy.CorrectCompiler.⟦_⟧
d_'10214'_'10215'_38 ::
  T_CorrectCompiler_4 -> AgdaAny -> Maybe AgdaAny
d_'10214'_'10215'_38 v0
  = case coe v0 of
      C_constructor_54 v5 v6 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CorrectCompiler.exec
d_exec_40 :: T_CorrectCompiler_4 -> AgdaAny -> AgdaAny -> AgdaAny
d_exec_40 v0
  = case coe v0 of
      C_constructor_54 v5 v6 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CorrectCompiler._≈_
d__'8776'__42 :: T_CorrectCompiler_4 -> AgdaAny -> AgdaAny -> ()
d__'8776'__42 = erased
-- Once.Adequacy.CorrectCompiler.compile
d_compile_44 ::
  T_CorrectCompiler_4 -> AgdaAny -> Bool -> AgdaAny -> Maybe AgdaAny
d_compile_44 v0
  = case coe v0 of
      C_constructor_54 v5 v6 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CorrectCompiler.correct
d_correct_52 ::
  T_CorrectCompiler_4 ->
  AgdaAny ->
  Bool ->
  AgdaAny ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_52 v0
  = case coe v0 of
      C_constructor_54 v5 v6 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
