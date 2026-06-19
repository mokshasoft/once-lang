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
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Eval.eval
d_eval_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_18 -> AgdaAny -> AgdaAny
d_eval_10 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_24 -> coe v3
      MAlonzo.Code.Once.CCC.IR.C__'8728'__32 v5 v7 v8
        -> coe
             d_eval_10 (coe v5) (coe v1) (coe v7)
             (coe d_eval_10 (coe v0) (coe v5) (coe v8) (coe v3))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_40 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v10 v11
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_306
                    (coe d_eval_10 (coe v0) (coe v10) (coe v7) (coe v3))
                    (coe d_eval_10 (coe v0) (coe v11) (coe v8) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_46
        -> coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_294 (coe v3)
      MAlonzo.Code.Once.CCC.IR.C_snd_52
        -> coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_300 (coe v3)
      MAlonzo.Code.Once.CCC.IR.C_inl_58 v6
        -> coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_316 v3
      MAlonzo.Code.Once.CCC.IR.C_inr_64 v6
        -> coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_322 v3
      MAlonzo.Code.Once.CCC.IR.C_case_72 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v9 v10
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_330
                    (coe d_eval_10 (coe v9) (coe v1) (coe v7))
                    (coe d_eval_10 (coe v10) (coe v1) (coe v8)) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_76
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.IR.C_curry_90 v8 v9
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
      MAlonzo.Code.Once.CCC.IR.C_apply_98
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8 -> coe v7 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_arr_106 -> coe v3
      MAlonzo.Code.Once.CCC.IR.C_In_110 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_920 (coe v7)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_94 (coe v7)
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_114 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v6
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_928 (coe v6)
                       (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Cata_120 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_940 v8 v5
                    (\ v9 ->
                       d_eval_10
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v8) (coe v1))
                         (coe v1) (coe v7)
                         (coe
                            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                            (coe v8) (coe v9)))
                    v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_126 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_956 (coe v8)
                    (coe v5)
                    (coe
                       (\ v9 ->
                          d_eval_10
                            (coe
                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v8)
                               (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                            (coe v1) (coe v7)
                            (coe
                               MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                               (coe v8) (coe v9))))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_130 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v6
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_990 (coe v6)
                       (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_134 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1000 (coe v7)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_94 (coe v7)
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Ana_140 v5 v7
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
                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v8) (coe v0))
                               (coe v7) (coe v9))))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_148 v4 v6 v7 v9 v10
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
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v4) (coe v1))
                         (coe v1) (coe v9)
                         (coe
                            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                            (coe v4) (coe v12)))
                    v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Fuse_156 v4 v6 v7 v9 v10
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
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v4) (coe v1))
                         (coe v1) (coe v9)
                         (coe
                            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
                            (coe v4) (coe v12)))
                    v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_158 v4 -> coe v3
      MAlonzo.Code.Once.CCC.IR.C_const_162 v5 v6
        -> coe seq (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.IR.C_SigOp_168 v6
        -> coe MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150 v6 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Eval.appNatTr-F
d_appNatTr'45'F_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_20 -> () -> AgdaAny -> AgdaAny
d_appNatTr'45'F_18 v0 v1 v2 ~v3 v4
  = du_appNatTr'45'F_18 v0 v1 v2 v4
du_appNatTr'45'F_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_20 -> AgdaAny -> AgdaAny
du_appNatTr'45'F_18 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_170 -> coe v3
      MAlonzo.Code.Once.CCC.IR.C_ntK_176 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v7
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v8
                      -> coe d_eval_10 (coe v7) (coe v8) (coe v6) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntFst_184 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatTr'45'F_18 (coe v8) (coe v1) (coe v7) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_192 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatTr'45'F_18 (coe v9) (coe v1) (coe v7) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntCase_200 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> coe du_appNatTr'45'F_18 (coe v9) (coe v1) (coe v7) (coe v11)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> coe du_appNatTr'45'F_18 (coe v10) (coe v1) (coe v8) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInl_208 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v8) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInr_216 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v9) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntPair_224 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v9) (coe v7) (coe v3))
                    (coe du_appNatTr'45'F_18 (coe v0) (coe v10) (coe v8) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
