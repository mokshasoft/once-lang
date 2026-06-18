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

module MAlonzo.Code.Once.CCC.Eval where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Eval.eval
d_eval_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278 -> AgdaAny -> AgdaAny
d_eval_10 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_284 -> coe v3
      MAlonzo.Code.Once.CCC.IR.C__'8728'__292 v5 v7 v8
        -> coe
             d_eval_10 (coe v5) (coe v1) (coe v7)
             (coe d_eval_10 (coe v0) (coe v5) (coe v8) (coe v3))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_300 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v10 v11
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320
                    (coe d_eval_10 (coe v0) (coe v10) (coe v7) (coe v3))
                    (coe d_eval_10 (coe v0) (coe v11) (coe v8) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_306
        -> coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_308 (coe v3)
      MAlonzo.Code.Once.CCC.IR.C_snd_312
        -> coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_314 (coe v3)
      MAlonzo.Code.Once.CCC.IR.C_inl_318 v6
        -> coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_330 v3
      MAlonzo.Code.Once.CCC.IR.C_inr_324 v6
        -> coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_336 v3
      MAlonzo.Code.Once.CCC.IR.C_case_332 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v9 v10
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_344
                    (coe d_eval_10 (coe v9) (coe v1) (coe v7))
                    (coe d_eval_10 (coe v10) (coe v1) (coe v8)) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_336
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.IR.C_curry_350 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    (\ v13 ->
                       d_eval_10
                         (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v10))
                         (coe v12) (coe v8)
                         (coe
                            MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320 (coe v3)
                            (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_358
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8 -> coe v7 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_arr_366 -> coe v3
      MAlonzo.Code.Once.CCC.IR.C_In_370 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_934 (coe v7)
                    (coe
                       MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 (coe v7)
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_374 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v6
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_942 (coe v6)
                       (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Cata_380 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v8 v5
                    (\ v9 ->
                       d_eval_10
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v8) (coe v1))
                         (coe v1) (coe v7)
                         (coe
                            MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                            (coe v8) (coe v9)))
                    v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_386 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_970 (coe v8)
                    (coe v5)
                    (coe
                       (\ v9 ->
                          d_eval_10
                            (coe
                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v8)
                               (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                            (coe v1) (coe v7)
                            (coe
                               MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                               (coe v8) (coe v9))))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_390 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v6
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1004 (coe v6)
                       (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_394 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1014 (coe v7)
                    (coe
                       MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 (coe v7)
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Ana_400 v5 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114 (coe v8)
                    (coe
                       (\ v9 ->
                          coe
                            MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 (coe v8)
                            (coe
                               d_eval_10 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v8) (coe v0))
                               (coe v7) (coe v9))))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_408 v4 v6 v7 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v11
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1244 v4 v11 v6
                    v7
                    (\ v12 v13 ->
                       coe du_appNatTr'45'F_18 (coe v11) (coe v4) (coe v10) v13)
                    (\ v12 ->
                       d_eval_10
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v4) (coe v1))
                         (coe v1) (coe v9)
                         (coe
                            MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                            (coe v4) (coe v12)))
                    v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Fuse_416 v4 v6 v7 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v11
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1244 v4 v11 v6
                    v7
                    (\ v12 v13 ->
                       coe du_appNatTr'45'F_18 (coe v11) (coe v4) (coe v10) v13)
                    (\ v12 ->
                       d_eval_10
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v4) (coe v1))
                         (coe v1) (coe v9)
                         (coe
                            MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                            (coe v4) (coe v12)))
                    v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_418 v4 -> coe v3
      MAlonzo.Code.Once.CCC.IR.C_const_422 v5 v6 v7 -> coe v7
      MAlonzo.Code.Once.CCC.IR.C_SigOp_428 v6
        -> coe MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166 v6 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Eval.appNatTr-F
d_appNatTr'45'F_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_280 -> () -> AgdaAny -> AgdaAny
d_appNatTr'45'F_18 v0 v1 v2 ~v3 v4
  = du_appNatTr'45'F_18 v0 v1 v2 v4
du_appNatTr'45'F_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_280 -> AgdaAny -> AgdaAny
du_appNatTr'45'F_18 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_430 -> coe v3
      MAlonzo.Code.Once.CCC.IR.C_ntK_436 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v7
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v8
                      -> coe d_eval_10 (coe v7) (coe v8) (coe v6) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntFst_444 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatTr'45'F_18 (coe v8) (coe v1) (coe v7) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_452 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatTr'45'F_18 (coe v9) (coe v1) (coe v7) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntCase_460 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> coe du_appNatTr'45'F_18 (coe v9) (coe v1) (coe v7) (coe v11)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> coe du_appNatTr'45'F_18 (coe v10) (coe v1) (coe v8) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInl_468 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v8) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInr_476 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v9) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntPair_484 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v9) (coe v7) (coe v3))
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v10) (coe v8) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
