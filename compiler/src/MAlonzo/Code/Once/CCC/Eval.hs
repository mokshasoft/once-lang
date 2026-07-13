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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Eval.eval
d_eval_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_eval_10 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe v3
      MAlonzo.Code.Once.IR.C__'8728'__30 v5 v7 v8
        -> coe
             d_eval_10 (coe v5) (coe v1) (coe v7)
             (coe d_eval_10 (coe v0) (coe v5) (coe v8) (coe v3))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v10 v11
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_306
                    (coe d_eval_10 (coe v0) (coe v10) (coe v7) (coe v3))
                    (coe d_eval_10 (coe v0) (coe v11) (coe v8) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_294 (coe v3)
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_300 (coe v3)
      MAlonzo.Code.Once.IR.C_inl_56 v6
        -> coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_316 v3
      MAlonzo.Code.Once.IR.C_inr_62 v6
        -> coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_322 v3
      MAlonzo.Code.Once.IR.C_case_70 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v9 v10
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_330
                    (coe d_eval_10 (coe v9) (coe v1) (coe v7))
                    (coe d_eval_10 (coe v10) (coe v1) (coe v8)) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_curry_88 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    (\ v13 ->
                       d_eval_10
                         (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v10))
                         (coe v12) (coe v8)
                         (coe
                            MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_306 (coe v3)
                            (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_96
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8 -> coe v7 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_arr_104 -> coe v3
      MAlonzo.Code.Once.IR.C_In_108 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_920 (coe v7)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_94 (coe v7)
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_112 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v6
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_928 (coe v6)
                       (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_118 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_940 v8 v5
                    (\ v9 ->
                       d_eval_10
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v8) (coe v1))
                         (coe v1) (coe v7)
                         (coe
                            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                            (coe v8) (coe v9)))
                    v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_124 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_956 (coe v8)
                    (coe v5)
                    (coe
                       (\ v9 ->
                          d_eval_10
                            (coe
                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v8)
                               (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                            (coe v1) (coe v7)
                            (coe
                               MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                               (coe v8) (coe v9))))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_128 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v6
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_990 (coe v6)
                       (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_132 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1000 (coe v7)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_94 (coe v7)
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_138 v5 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1024 (coe v8)
                    (coe
                       (\ v9 ->
                          coe
                            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_94 (coe v8)
                            (coe
                               d_eval_10 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v8) (coe v0))
                               (coe v7) (coe v9))))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Hylo_146 v4 v6 v7 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v11
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1154 v4 v11 v6
                    v7
                    (\ v12 v13 ->
                       coe du_appNatTr'45'F_18 (coe v11) (coe v4) (coe v10) v13)
                    (\ v12 ->
                       d_eval_10
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v4) (coe v1))
                         (coe v1) (coe v9)
                         (coe
                            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                            (coe v4) (coe v12)))
                    v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Fuse_154 v4 v6 v7 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v11
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1154 v4 v11 v6
                    v7
                    (\ v12 v13 ->
                       coe du_appNatTr'45'F_18 (coe v11) (coe v4) (coe v10) v13)
                    (\ v12 ->
                       d_eval_10
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v4) (coe v1))
                         (coe v1) (coe v9)
                         (coe
                            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                            (coe v4) (coe v12)))
                    v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_free'45'heap_156 v4 -> coe v3
      MAlonzo.Code.Once.IR.C_const_160 v5 v6 -> coe seq (coe v5) (coe v6)
      MAlonzo.Code.Once.IR.C_SigOp_166 v6
        -> coe MAlonzo.Code.Once.SigOp.Info.du_semM_188 v6 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Eval.appNatTr-F
d_appNatTr'45'F_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> () -> AgdaAny -> AgdaAny
d_appNatTr'45'F_18 v0 v1 v2 ~v3 v4
  = du_appNatTr'45'F_18 v0 v1 v2 v4
du_appNatTr'45'F_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> AgdaAny -> AgdaAny
du_appNatTr'45'F_18 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_168 -> coe v3
      MAlonzo.Code.Once.IR.C_ntK_174 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v7
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v8
                      -> coe d_eval_10 (coe v7) (coe v8) (coe v6) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_182 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatTr'45'F_18 (coe v8) (coe v1) (coe v7) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_190 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatTr'45'F_18 (coe v9) (coe v1) (coe v7) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_198 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> coe du_appNatTr'45'F_18 (coe v9) (coe v1) (coe v7) (coe v11)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> coe du_appNatTr'45'F_18 (coe v10) (coe v1) (coe v8) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_206 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v8) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_214 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v9) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_222 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v9) (coe v7) (coe v3))
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v10) (coe v8) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
