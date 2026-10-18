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

module MAlonzo.Code.Once.Lang.Equivalence where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Lang.Graded
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Stream
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade

-- Once.Lang.Equivalence.TreeEq
d_TreeEq_10 a0 a1 a2 a3 = ()
data T_TreeEq_10
  = C_ret'8776'_20 AgdaAny |
    C_call'8776'_32 (AgdaAny -> T_TreeEq_10) | C_halt'8776'_38
-- Once.Lang.Equivalence.TreeEqN
d_TreeEqN_42 ::
  () ->
  Integer ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 -> ()
d_TreeEqN_42 = erased
-- Once.Lang.Equivalence.LayerEq
d_LayerEq_58 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_LayerEq_58 = erased
-- Once.Lang.Equivalence.νᵖ-upto
d_ν'7510''45'upto_122 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_198 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_198 -> ()
d_ν'7510''45'upto_122 = erased
-- Once.Lang.Equivalence.νᵈ-upto
d_ν'7496''45'upto_136 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 -> ()
d_ν'7496''45'upto_136 = erased
-- Once.Lang.Equivalence.ν∞-upto
d_ν'8734''45'upto_150 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Iterative.T_ν'8734'_304 ->
  MAlonzo.Code.Once.Lang.Iterative.T_ν'8734'_304 -> ()
d_ν'8734''45'upto_150 = erased
-- Once.Lang.Equivalence.Obs
d_Obs_164 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_Obs_164 = erased
-- Once.Lang.Equivalence.ObsM
d_ObsM_170 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_ObsM_170 = erased
-- Once.Lang.Equivalence.Same
d_Same_320 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_Same_320 = erased
-- Once.Lang.Equivalence.SameM
d_SameM_334 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_SameM_334 = erased
