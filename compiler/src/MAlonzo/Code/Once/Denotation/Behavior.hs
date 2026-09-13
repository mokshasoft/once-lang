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

module MAlonzo.Code.Once.Denotation.Behavior where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.Trace

-- Once.Denotation.Behavior.Behavior
d_Behavior_6 = ()
data T_Behavior_6
  = C_mkBehavior_40 (Integer ->
                     [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
                    (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                    (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Denotation.Behavior.Behavior.at
d_at_24 ::
  T_Behavior_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_at_24 v0
  = case coe v0 of
      C_mkBehavior_40 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Behavior.Behavior.extends
d_extends_30 ::
  T_Behavior_6 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extends_30 v0
  = case coe v0 of
      C_mkBehavior_40 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Behavior.Behavior.bounded
d_bounded_34 ::
  T_Behavior_6 -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bounded_34 v0
  = case coe v0 of
      C_mkBehavior_40 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Behavior.Behavior.saturates
d_saturates_38 ::
  T_Behavior_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_saturates_38 = erased
-- Once.Denotation.Behavior.silent
d_silent_42 :: T_Behavior_6
d_silent_42
  = coe
      C_mkBehavior_40
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (\ v0 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased)
      (\ v0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Denotation.Behavior.behavior-by
d_behavior'45'by_50 ::
  T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_Behavior_6
d_behavior'45'by_50 v0 v1 ~v2 = du_behavior'45'by_50 v0 v1
du_behavior'45'by_50 ::
  T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  T_Behavior_6
du_behavior'45'by_50 v0 v1
  = coe
      C_mkBehavior_40 v1 (coe du_ext_66 (coe v0))
      (coe du_bnd_74 (coe v0))
-- Once.Denotation.Behavior._.ext
d_ext_66 ::
  T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ext_66 v0 ~v1 ~v2 v3 = du_ext_66 v0 v3
du_ext_66 ::
  T_Behavior_6 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ext_66 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_extends_30 v0 v1))
      erased
-- Once.Denotation.Behavior._.bnd
d_bnd_74 ::
  T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_74 v0 ~v1 ~v2 v3 = du_bnd_74 v0 v3
du_bnd_74 ::
  T_Behavior_6 -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd_74 v0 v1 = coe d_bounded_34 v0 v1
-- Once.Denotation.Behavior._.sat
d_sat_82 ::
  T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat_82 = erased
-- Once.Denotation.Behavior.take-all
d_take'45'all_94 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'all_94 = erased
-- Once.Denotation.Behavior.take-++-≤
d_take'45''43''43''45''8804'_114 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45''43''43''45''8804'_114 = erased
-- Once.Denotation.Behavior.step
d_step_138 ::
  T_Behavior_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step_138 = erased
-- Once.Denotation.Behavior._.go
d_go_152 ::
  T_Behavior_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_152 = erased
-- Once.Denotation.Behavior.at-stable
d_at'45'stable_176 ::
  T_Behavior_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'stable_176 = erased
-- Once.Denotation.Behavior._.go
d_go_192 ::
  T_Behavior_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_192 = erased
-- Once.Denotation.Behavior.Source
d_Source_196 = ()
data T_Source_196
  = C_mkSource_206 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                   MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Denotation.Behavior.Source.srcImports
d_srcImports_202 ::
  T_Source_196 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_srcImports_202 v0
  = case coe v0 of
      C_mkSource_206 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Behavior.Source.srcText
d_srcText_204 ::
  T_Source_196 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_srcText_204 v0
  = case coe v0 of
      C_mkSource_206 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
