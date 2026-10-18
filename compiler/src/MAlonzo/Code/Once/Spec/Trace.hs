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

module MAlonzo.Code.Once.Spec.Trace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Delay
import qualified MAlonzo.Code.Once.Spec.Signature

-- Once.Spec.Trace.End
d_End_8 a0 = ()
data T_End_8 = C_returned_12 AgdaAny | C_halted_14
-- Once.Spec.Trace.Tr
d_Tr_18 a0 = ()
data T_Tr_18
  = C_constructor_26 MAlonzo.Code.Once.Spec.Delay.T_Delay_8
-- Once.Spec.Trace.Tr.next
d_next_24 :: T_Tr_18 -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8
d_next_24 v0
  = case coe v0 of
      C_constructor_26 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Trace.EndRel
d_EndRel_32 a0 a1 a2 a3 = ()
data T_EndRel_32 = C_returned'8776'_42 AgdaAny | C_halted'8776'_44
-- Once.Spec.Trace.StepRel
d_StepRel_48 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (T_Tr_18 -> T_Tr_18 -> ()) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_StepRel_48 = erased
-- Once.Spec.Trace._≈ᵗ⟨_⟩_
d__'8776''7511''10216'_'10217'__86 a0 a1 a2 a3 = ()
data T__'8776''7511''10216'_'10217'__86
  = C_constructor_108 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Spec.Trace._≈ᵗ⟨_⟩_.same
d_same_106 ::
  T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_same_106 v0
  = case coe v0 of
      C_constructor_108 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Trace.Calls
d_Calls_112 a0 a1 a2 = ()
data T_Calls_112
  = C_none_118 |
    C_call_128 T_Tr_18 MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
               T_Calls_112
