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
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.FrameSemantics.FrameSemantics
d_FrameSemantics_6 = ()
data T_FrameSemantics_6
  = C_constructor_160 (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                      (AgdaAny -> Integer) (AgdaAny -> Integer -> Integer)
                      (AgdaAny -> Integer -> AgdaAny) Integer
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                      MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
                      MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Once.CCC.FrameSemantics.FrameSemantics.Frame
d_Frame_84 :: T_FrameSemantics_6 -> ()
d_Frame_84 = erased
-- Once.CCC.FrameSemantics.FrameSemantics._≟F_
d__'8799'F__90 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__90 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-base
d_frame'45'base_92 :: T_FrameSemantics_6 -> AgdaAny -> Integer
d_frame'45'base_92 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.slot-addr
d_slot'45'addr_94 ::
  T_FrameSemantics_6 -> AgdaAny -> Integer -> Integer
d_slot'45'addr_94 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_98 ::
  T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_98 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.slot-injective
d_slot'45'injective_106 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_106 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.shift-frame
d_shift'45'frame_108 ::
  T_FrameSemantics_6 -> AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_108 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-word
d_frame'45'word_110 :: T_FrameSemantics_6 -> Integer
d_frame'45'word_110 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_112 ::
  T_FrameSemantics_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_112 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_118 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_118 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.shift-base
d_shift'45'base_124 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_124 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.float-format
d_float'45'format_126 ::
  T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_126 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.fs-interp
d_fs'45'interp_128 ::
  T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_fs'45'interp_128 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics._≺_
d__'8826'__130 :: T_FrameSemantics_6 -> AgdaAny -> AgdaAny -> ()
d__'8826'__130 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.≺-trans
d_'8826''45'trans_138 ::
  T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_138 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_142 ::
  T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_142 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.≺-compare
d_'8826''45'compare_148 ::
  T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_148 v0
  = case coe v0 of
      C_constructor_160 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_158 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_158 = erased
-- Once.CCC.FrameSemantics.fs-ffi
d_fs'45'ffi_162 ::
  T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_fs'45'ffi_162 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_540
      (coe d_fs'45'interp_128 (coe v0))
-- Once.CCC.FrameSemantics.fs-numerics
d_fs'45'numerics_166 ::
  T_FrameSemantics_6 -> MAlonzo.Code.Once.Target.Arch.T_TargetNum_14
d_fs'45'numerics_166 v0
  = coe
      MAlonzo.Code.Once.Target.Arch.C_mkTargetNum_28
      (coe
         mulInt (coe (8 :: Integer)) (coe d_frame'45'word_110 (coe v0)))
      (coe d_float'45'format_126 (coe v0))
      (coe d_bits'45'pos_174 (coe v0))
-- Once.CCC.FrameSemantics._.bits-pos
d_bits'45'pos_174 ::
  T_FrameSemantics_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bits'45'pos_174 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'45''8804'_4214
      (coe (8 :: Integer)) (coe d_frame'45'word_110 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe d_frame'45'word'45'pos_112 (coe v0))
