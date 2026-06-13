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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Eval
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Core
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
-- Once.Verified.TraceDenote.cata-ev-alg
d_cata'45'ev'45'alg_50 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'ev'45'alg_50 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            du_events'45'F_10 (coe v0)
            (coe (\ v5 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
            (coe v4))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_obs_56
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
               (coe v1) (coe v2) (coe v3) (coe du_z_234 (coe v0) (coe v4)))))
      (coe
         MAlonzo.Code.Once.CCC.Eval.d_eval_10
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
         (coe v1) (coe v3) (coe du_z_234 (coe v0) (coe v4)))
-- Once.Verified.TraceDenote.obs
d_obs_56 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_obs_56 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
              (coe
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                 (coe
                    MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v0) (coe v1) (coe v3)
                    (coe v4))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v7 v9 v10
           -> let v11
                    = d_obs_56 (coe v0) (coe v7) (coe v2) (coe v10) (coe v4) in
              coe
                (case coe v11 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                     -> case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                            -> let v15
                                     = d_obs_56 (coe v7) (coe v1) (coe v2) (coe v9) (coe v14) in
                               coe
                                 (case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v12)
                                              (coe v16))
                                           (coe v17)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294 v9 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
                  -> let v14
                           = d_obs_56 (coe v0) (coe v12) (coe v2) (coe v9) (coe v4) in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                            -> case coe v16 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                   -> let v18
                                            = d_obs_56
                                                (coe v0) (coe v13) (coe v2) (coe v10) (coe v4) in
                                      coe
                                        (case coe v18 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                             -> case coe v20 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                            (coe v15) (coe v19))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe
                                                               MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320
                                                               (coe v17) (coe v21)))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                            (coe v15) (coe v19))
                                                         (coe v20)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v14
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_case_326 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                  -> case coe v4 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                         -> coe d_obs_56 (coe v11) (coe v1) (coe v2) (coe v9) (coe v13)
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                         -> coe d_obs_56 (coe v12) (coe v1) (coe v2) (coe v10) (coe v13)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_Cata_374 v7 v9
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v10 v7
                             (d_cata'45'ev'45'alg_50 (coe v10) (coe v1) (coe v2) (coe v9)) v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.CCC.IR.C_Cata_374 v7 v9) (coe v4)))
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_SigOp_422 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Verified.Trace.du_mkEvent_152 (coe v0) (coe v8)
                      (coe v4))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_294 v8 v4))
         _ -> coe v5)
-- Once.Verified.TraceDenote._.z
d_z_234 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer -> MAlonzo.Code.Once.CCC.IR.T_IR_274 -> AgdaAny -> AgdaAny
d_z_234 v0 ~v1 ~v2 ~v3 v4 = du_z_234 v0 v4
du_z_234 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_z_234 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 (coe v0)
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
         (coe v1))
-- Once.Verified.TraceDenote.obs-cata-value
d_obs'45'cata'45'value_248 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_obs'45'cata'45'value_248 = erased
-- Once.Verified.TraceDenote.EmitsNoSigOp
d_EmitsNoSigOp_262 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> ()
d_EmitsNoSigOp_262 = erased
