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

module MAlonzo.Code.Once.Verified.TraceDenote where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Verified.Trace

-- Once.Verified.TraceDenote.events-F
d_events'45'F_10 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]) ->
  AgdaAny -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_events'45'F_10 v0 ~v1 v2 v3 = du_events'45'F_10 v0 v2 v3
du_events'45'F_10 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]) ->
  AgdaAny -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
du_events'45'F_10 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__118 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe du_events'45'F_10 (coe v3) (coe v1) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe du_events'45'F_10 (coe v4) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe du_events'45'F_10 (coe v3) (coe v1) (coe v5))
                    (coe du_events'45'F_10 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.TraceDenote.sig1
d_sig1_46 ::
  Integer ->
  MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_sig1_46 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Verified.TraceDenote.emit-eff
d_emit'45'eff_54 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_150 ->
  Integer ->
  AgdaAny -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_emit'45'eff_54 v0 ~v1 v2 v3 v4 = du_emit'45'eff_54 v0 v2 v3 v4
du_emit'45'eff_54 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_150 ->
  Integer ->
  AgdaAny -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
du_emit'45'eff_54 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.CCC.SigOp.Info.d_effect_166 (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_140
           -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         MAlonzo.Code.Once.CCC.SigOp.Info.C_Emits_142
           -> coe
                d_sig1_46 (coe v2)
                (coe
                   MAlonzo.Code.Once.Verified.Trace.du_mkEvent_152 (coe v0) (coe v1)
                   (coe v3))
         MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_144
           -> coe
                d_sig1_46 (coe v2)
                (coe
                   MAlonzo.Code.Once.Verified.Trace.du_mkEvent_152 (coe v0) (coe v1)
                   (coe v3))
         _ -> MAlonzo.RTE.mazUnreachableError)
