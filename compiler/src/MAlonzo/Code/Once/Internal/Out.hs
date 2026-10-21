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

module MAlonzo.Code.Once.Internal.Out where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Spec.Trace

-- Once.Internal.Out.Out
d_Out_6 :: ()
d_Out_6 = erased
-- Once.Internal.Out.cut
d_cut_8 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cut_8
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.Internal.Out.ended
d_ended_10 ::
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ended_10 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0))
-- Once.Internal.Out._▹_
d__'9657'__14 ::
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'9657'__14 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
-- Once.Internal.Out.▹-assoc
d_'9657''45'assoc_26 ::
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9657''45'assoc_26 = erased
-- Once.Internal.Out.stop
d_stop_36 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stop_36
  = coe d_ended_10 (coe MAlonzo.Code.Once.Spec.Trace.C_halted_14)
-- Once.Internal.Out.end-of-left
d_end'45'of'45'left_38 ::
  Bool -> MAlonzo.Code.Once.Spec.Trace.T_End_8
d_end'45'of'45'left_38 v0
  = if coe v0
      then coe
             MAlonzo.Code.Once.Spec.Trace.C_returned_12
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      else coe MAlonzo.Code.Once.Spec.Trace.C_halted_14
