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
import qualified MAlonzo.Code.Once.IR.Semantics.Trace
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.FrameSemantics.FrameSemantics
d_FrameSemantics_6 = ()
data T_FrameSemantics_6
  = C_constructor_152 (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                      (AgdaAny -> Integer) (AgdaAny -> Integer -> Integer)
                      (AgdaAny -> Integer -> AgdaAny) Integer
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                      MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
                      MAlonzo.Code.Once.IR.Semantics.Trace.T_Interp_184
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Once.CCC.FrameSemantics.FrameSemantics.Frame
d_Frame_80 :: T_FrameSemantics_6 -> ()
d_Frame_80 = erased
-- Once.CCC.FrameSemantics.FrameSemantics._≟F_
d__'8799'F__82 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__82 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-base
d_frame'45'base_84 :: T_FrameSemantics_6 -> AgdaAny -> Integer
d_frame'45'base_84 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.slot-addr
d_slot'45'addr_86 ::
  T_FrameSemantics_6 -> AgdaAny -> Integer -> Integer
d_slot'45'addr_86 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_90 ::
  T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_90 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.slot-injective
d_slot'45'injective_98 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_98 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.shift-frame
d_shift'45'frame_100 ::
  T_FrameSemantics_6 -> AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_100 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-word
d_frame'45'word_102 :: T_FrameSemantics_6 -> Integer
d_frame'45'word_102 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_104 ::
  T_FrameSemantics_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_104 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_110 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_110 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.shift-base
d_shift'45'base_116 ::
  T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_116 = erased
-- Once.CCC.FrameSemantics.FrameSemantics.float-format
d_float'45'format_118 ::
  T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
d_float'45'format_118 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.FrameSemantics.FrameSemantics.fs-interp
d_fs'45'interp_120 ::
  T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_Interp_184
d_fs'45'interp_120 v0
  = case coe v0 of
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v13
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
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v15
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
      C_constructor_152 v2 v3 v4 v7 v8 v9 v12 v13 v15 v17 -> coe v17
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
-- Once.CCC.FrameSemantics.fs-ffi
d_fs'45'ffi_154 ::
  T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_fs'45'ffi_154 v0
  = coe
      MAlonzo.Code.Once.IR.Semantics.Trace.d_pureHalf_264
      (coe d_fs'45'interp_120 (coe v0))
-- Once.CCC.FrameSemantics.fs-numerics
d_fs'45'numerics_158 ::
  T_FrameSemantics_6 -> MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6
d_fs'45'numerics_158 v0
  = coe
      MAlonzo.Code.Once.Spec.Numerics.C_mkTargetNum_20
      (coe
         mulInt (coe (8 :: Integer)) (coe d_frame'45'word_102 (coe v0)))
      (coe d_float'45'format_118 (coe v0))
      (coe d_bits'45'pos_166 (coe v0))
-- Once.CCC.FrameSemantics._.bits-pos
d_bits'45'pos_166 ::
  T_FrameSemantics_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bits'45'pos_166 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'45''8804'_4214
      (coe (8 :: Integer)) (coe d_frame'45'word_102 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe d_frame'45'word'45'pos_104 (coe v0))
