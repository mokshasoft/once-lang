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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Eval
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Verified.Trace

-- Once.Verified.TraceDenote.obs
d_obs_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_obs_10 v0 v1 ~v2 v3 v4 = du_obs_10 v0 v1 v3 v4
du_obs_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_obs_10 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
              (coe
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                 (coe
                    MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v0) (coe v1) (coe v2)
                    (coe v3))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v6 v8 v9
           -> let v10 = coe du_obs_10 (coe v0) (coe v6) (coe v9) (coe v3) in
              coe
                (case coe v10 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                     -> case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                            -> let v14 = coe du_obs_10 (coe v6) (coe v1) (coe v8) (coe v13) in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v11)
                                              (coe v15))
                                           (coe v16)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294 v8 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                  -> let v13 = coe du_obs_10 (coe v0) (coe v11) (coe v8) (coe v3) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                   -> let v17
                                            = coe du_obs_10 (coe v0) (coe v12) (coe v9) (coe v3) in
                                      coe
                                        (case coe v17 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                             -> case coe v19 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                            (coe v14) (coe v18))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe
                                                               MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320
                                                               (coe v16) (coe v20)))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                            (coe v14) (coe v18))
                                                         (coe v19)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v13
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_case_326 v8 v9
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
                  -> case coe v3 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                         -> coe du_obs_10 (coe v10) (coe v1) (coe v8) (coe v12)
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                         -> coe du_obs_10 (coe v11) (coe v1) (coe v9) (coe v12)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_SigOp_422 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Verified.Trace.du_mkEvent_152 (coe v0) (coe v7)
                      (coe v3))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_294 v7 v3))
         _ -> coe v4)
