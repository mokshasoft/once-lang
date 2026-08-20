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
import qualified MAlonzo.Code.Agda.Builtin.Sigma

-- Once.Adequacy.CorrectCompiler
d_CorrectCompiler_4 = ()
data T_CorrectCompiler_4
  = C_constructor_78 (AgdaAny -> AgdaAny -> AgdaAny)
                     (AgdaAny -> AgdaAny -> AgdaAny)
                     (AgdaAny -> Bool -> AgdaAny -> Maybe AgdaAny)
                     (AgdaAny ->
                      Bool -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Adequacy.CorrectCompiler.Arch
d_Arch_42 :: T_CorrectCompiler_4 -> ()
d_Arch_42 = erased
-- Once.Adequacy.CorrectCompiler.Source
d_Source_44 :: T_CorrectCompiler_4 -> ()
d_Source_44 = erased
-- Once.Adequacy.CorrectCompiler.Bytes
d_Bytes_46 :: T_CorrectCompiler_4 -> ()
d_Bytes_46 = erased
-- Once.Adequacy.CorrectCompiler.Behavior
d_Behavior_48 :: T_CorrectCompiler_4 -> ()
d_Behavior_48 = erased
-- Once.Adequacy.CorrectCompiler.Typed
d_Typed_50 :: T_CorrectCompiler_4 -> ()
d_Typed_50 = erased
-- Once.Adequacy.CorrectCompiler._⊢_
d__'8866'__52 :: T_CorrectCompiler_4 -> AgdaAny -> AgdaAny -> ()
d__'8866'__52 = erased
-- Once.Adequacy.CorrectCompiler.⟦_⟧ˢ
d_'10214'_'10215''738'_54 ::
  T_CorrectCompiler_4 -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214'_'10215''738'_54 v0
  = case coe v0 of
      C_constructor_78 v7 v8 v10 v11 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CorrectCompiler.exec
d_exec_56 :: T_CorrectCompiler_4 -> AgdaAny -> AgdaAny -> AgdaAny
d_exec_56 v0
  = case coe v0 of
      C_constructor_78 v7 v8 v10 v11 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CorrectCompiler._≈_
d__'8776'__58 :: T_CorrectCompiler_4 -> AgdaAny -> AgdaAny -> ()
d__'8776'__58 = erased
-- Once.Adequacy.CorrectCompiler.compile
d_compile_60 ::
  T_CorrectCompiler_4 -> AgdaAny -> Bool -> AgdaAny -> Maybe AgdaAny
d_compile_60 v0
  = case coe v0 of
      C_constructor_78 v7 v8 v10 v11 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CorrectCompiler.correct
d_correct_76 ::
  T_CorrectCompiler_4 ->
  AgdaAny ->
  Bool -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correct_76 v0
  = case coe v0 of
      C_constructor_78 v7 v8 v10 v11 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
