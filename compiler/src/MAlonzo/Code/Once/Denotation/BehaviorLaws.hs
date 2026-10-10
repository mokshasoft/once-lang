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

module MAlonzo.Code.Once.Denotation.BehaviorLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Trace

-- Once.Denotation.BehaviorLaws.behavior-by
d_behavior'45'by_12 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_behavior'45'by_12 v0 v1 ~v2 = du_behavior'45'by_12 v0 v1
du_behavior'45'by_12 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_behavior'45'by_12 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Behavior.C_mkBehavior_40 v1
      (coe du_ext_28 (coe v0)) (coe du_bnd_36 (coe v0))
-- Once.Denotation.BehaviorLaws._.ext
d_ext_28 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ext_28 v0 ~v1 ~v2 v3 = du_ext_28 v0 v3
du_ext_28 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ext_28 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe MAlonzo.Code.Once.Denotation.Behavior.d_extends_30 v0 v1))
      erased
-- Once.Denotation.BehaviorLaws._.bnd
d_bnd_36 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_36 v0 ~v1 ~v2 v3 = du_bnd_36 v0 v3
du_bnd_36 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd_36 v0 v1
  = coe MAlonzo.Code.Once.Denotation.Behavior.d_bounded_34 v0 v1
-- Once.Denotation.BehaviorLaws._.sat
d_sat_44 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat_44 = erased
-- Once.Denotation.BehaviorLaws.take-all
d_take'45'all_56 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'all_56 = erased
-- Once.Denotation.BehaviorLaws.take-++-≤
d_take'45''43''43''45''8804'_76 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45''43''43''45''8804'_76 = erased
-- Once.Denotation.BehaviorLaws.step
d_step_100 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step_100 = erased
-- Once.Denotation.BehaviorLaws._.go
d_go_114 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_114 = erased
-- Once.Denotation.BehaviorLaws.at-stable
d_at'45'stable_138 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'stable_138 = erased
-- Once.Denotation.BehaviorLaws._.go
d_go_154 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_154 = erased
