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

module MAlonzo.Code.Once.Spec.Correct where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma

-- Once.Spec.Correct.CorrectCompiler
d_CorrectCompiler_6 = ()
data T_CorrectCompiler_6
  = C_constructor_108 (AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> Bool -> AgdaAny -> Maybe AgdaAny)
                      (AgdaAny ->
                       Bool -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Spec.Correct.CorrectCompiler.Arch
d_Arch_58 :: T_CorrectCompiler_6 -> ()
d_Arch_58 = erased
-- Once.Spec.Correct.CorrectCompiler.Source
d_Source_60 :: T_CorrectCompiler_6 -> ()
d_Source_60 = erased
-- Once.Spec.Correct.CorrectCompiler.Bytes
d_Bytes_62 :: T_CorrectCompiler_6 -> ()
d_Bytes_62 = erased
-- Once.Spec.Correct.CorrectCompiler.Behavior
d_Behavior_64 :: T_CorrectCompiler_6 -> ()
d_Behavior_64 = erased
-- Once.Spec.Correct.CorrectCompiler.Signature
d_Signature_66 :: T_CorrectCompiler_6 -> ()
d_Signature_66 = erased
-- Once.Spec.Correct.CorrectCompiler.Implementation
d_Implementation_68 :: T_CorrectCompiler_6 -> AgdaAny -> ()
d_Implementation_68 = erased
-- Once.Spec.Correct.CorrectCompiler.Typed
d_Typed_70 :: T_CorrectCompiler_6 -> ()
d_Typed_70 = erased
-- Once.Spec.Correct.CorrectCompiler._⊢_
d__'8866'__72 :: T_CorrectCompiler_6 -> AgdaAny -> AgdaAny -> ()
d__'8866'__72 = erased
-- Once.Spec.Correct.CorrectCompiler.sigOf
d_sigOf_74 :: T_CorrectCompiler_6 -> AgdaAny -> AgdaAny
d_sigOf_74 v0
  = case coe v0 of
      C_constructor_108 v9 v10 v11 v14 v15 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Correct.CorrectCompiler.⟦_⟧ˢ
d_'10214'_'10215''738'_78 ::
  T_CorrectCompiler_6 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214'_'10215''738'_78 v0
  = case coe v0 of
      C_constructor_108 v9 v10 v11 v14 v15 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Correct.CorrectCompiler.exec
d_exec_82 ::
  T_CorrectCompiler_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_exec_82 v0
  = case coe v0 of
      C_constructor_108 v9 v10 v11 v14 v15 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Correct.CorrectCompiler._≈_
d__'8776'__84 :: T_CorrectCompiler_6 -> AgdaAny -> AgdaAny -> ()
d__'8776'__84 = erased
-- Once.Spec.Correct.CorrectCompiler.Admissible
d_Admissible_86 :: T_CorrectCompiler_6 -> AgdaAny -> AgdaAny -> ()
d_Admissible_86 = erased
-- Once.Spec.Correct.CorrectCompiler.compile
d_compile_88 ::
  T_CorrectCompiler_6 -> AgdaAny -> Bool -> AgdaAny -> Maybe AgdaAny
d_compile_88 v0
  = case coe v0 of
      C_constructor_108 v9 v10 v11 v14 v15 -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Correct.CorrectCompiler.correct
d_correct_106 ::
  T_CorrectCompiler_6 ->
  AgdaAny ->
  Bool -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correct_106 v0
  = case coe v0 of
      C_constructor_108 v9 v10 v11 v14 v15 -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
