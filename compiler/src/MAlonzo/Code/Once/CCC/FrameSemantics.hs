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

module MAlonzo.Code.Once.CCC.FrameSemantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.FrameSemantics.FrameSemantics
d_FrameSemantics_6 = ()
data T_FrameSemantics_6
  = C_constructor_152 (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                      (AgdaAny -> Integer) (AgdaAny -> Integer -> Integer)
                      (AgdaAny -> Integer -> AgdaAny) Integer
                      MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Once.CCC.FrameSemantics.FrameSemantics.Frame
d_Frame_80 :: T_FrameSemantics_6 -> ()
d_Frame_80 = erased
-- Once.CCC.FrameSemantics.FrameSemantics._≟F_
d__'8799'F__86 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__86 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v11 v13 v15 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-base
d_frame'45'base_88 :: T_FrameSemantics_6 -> AgdaAny -> Integer
d_frame'45'base_88 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v11 v13 v15 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.slot-addr
d_slot'45'addr_90 ::
  T_FrameSemantics_6 -> AgdaAny -> Integer -> Integer
d_slot'45'addr_90 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v11 v13 v15 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_94 ::
  T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_94 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.slot-injective
d_slot'45'injective_102 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_102 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.shift-frame
d_shift'45'frame_104 ::
  T_FrameSemantics_6 -> AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_104 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v11 v13 v15 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-word
d_frame'45'word_106 :: T_FrameSemantics_6 -> Integer
d_frame'45'word_106 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v11 v13 v15 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_112 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_112 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.shift-base
d_shift'45'base_118 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_118 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.float-format
d_float'45'format_120 ::
  T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_120 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v11 v13 v15 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics._≺_
d__'8826'__122 :: T_FrameSemantics_6 -> AgdaAny -> AgdaAny -> ()
d__'8826'__122 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.≺-trans
d_'8826''45'trans_130 ::
  T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_130 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v11 v13 v15 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_134 ::
  T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_134 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.≺-compare
d_'8826''45'compare_140 ::
  T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_140 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v11 v13 v15 -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_150 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_150 = erased
-- Once.CCC.FrameSemantics.fs-numerics
d_fs'45'numerics_154 ::
  T_FrameSemantics_6 -> MAlonzo.Code.Once.Target.Arch.T_TargetNum_14
d_fs'45'numerics_154 v0
  = coe
      MAlonzo.Code.Once.Target.Arch.C_mkTargetNum_24
      (coe
         mulInt (coe (8 :: Integer)) (coe d_frame'45'word_106 (coe v0)))
      (coe d_float'45'format_120 (coe v0))
