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

module MAlonzo.Code.Once.Denotation.TraceDenote where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.Denotation.TraceDenote.events-F
d_events'45'F_10 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_events'45'F_10 v0 ~v1 v2 v3 = du_events'45'F_10 v0 v2 v3
du_events'45'F_10 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
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
-- Once.Denotation.TraceDenote.sig1
d_sig1_46 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_sig1_46 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Denotation.TraceDenote.emit-eff
d_emit'45'eff_54 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  Integer ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_emit'45'eff_54 v0 ~v1 v2 v3 v4 = du_emit'45'eff_54 v0 v2 v3 v4
du_emit'45'eff_54 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  Integer ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_emit'45'eff_54 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.SigOp.Info.du_go_228
              (coe MAlonzo.Code.Once.SigOp.Info.d_sem_176 (coe v1)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.SigOp.Info.C_Pure_124
           -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         MAlonzo.Code.Once.SigOp.Info.C_Emits_126
           -> coe
                d_sig1_46 (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Trace.du_mkEvent_142 (coe v0) (coe v1)
                   (coe v3))
         MAlonzo.Code.Once.SigOp.Info.C_Halts_128
           -> coe
                d_sig1_46 (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Trace.du_mkEvent_142 (coe v0) (coe v1)
                   (coe v3))
         _ -> MAlonzo.RTE.mazUnreachableError)
