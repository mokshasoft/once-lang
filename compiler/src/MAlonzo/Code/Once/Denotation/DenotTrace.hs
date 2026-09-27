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

module MAlonzo.Code.Once.Denotation.DenotTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word

-- Once.Denotation.DenotTrace.evalᴰ
d_eval'7472'_12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_eval'7472'_12 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34 (coe v4)
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__70
             (coe d_eval'7472'_12 (coe v0) (coe v1) (coe v6) (coe v9) (coe v4))
             (coe d_eval'7472'_12 (coe v0) (coe v6) (coe v2) (coe v8))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__70
                    (coe d_eval'7472'_12 (coe v0) (coe v1) (coe v10) (coe v8) (coe v4))
                    (coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__70
                            (coe d_eval'7472'_12 (coe v0) (coe v1) (coe v11) (coe v9) (coe v4))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                       (coe v13))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4))
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4))
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe
                           d_eval'7472'_12 (coe v0) (coe v10) (coe v2) (coe v8) (coe v12)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> coe
                           d_eval'7472'_12 (coe v0) (coe v11) (coe v2) (coe v9) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.IR.C_curry_84 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
                    (coe
                       (\ v11 ->
                          d_eval'7472'_12
                            (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v9))
                            (coe v10) (coe v8)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v11))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v4
             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
      MAlonzo.Code.Once.IR.C_In_94 v6
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
                    (coe (\ v8 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                    (coe
                       MAlonzo.Code.Once.Res.C_returns_12
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_514
                          (coe
                             MAlonzo.Code.Once.Type.C_μ'45'type_128
                             (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v7)))
                          (coe
                             d_in'45'val_16 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_622
                                   (coe
                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v7)
                                      (coe v2)))
                                (coe v4)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
                    (coe (\ v8 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                    (coe
                       MAlonzo.Code.Once.Res.C_returns_12
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_514
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_622
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v7) (coe v1)))
                          (coe
                             d_out'45'μ'45'val_20 (coe v7) (coe v6)
                             (coe
                                MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
                                (coe
                                   MAlonzo.Code.Once.Type.C_μ'45'type_128
                                   (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v7)))
                                (coe v4)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v6 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_956
                           (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v12))
                           (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                              (coe v12) (coe v6))
                           (d_cata'45'ev'45'alg'7472'_36
                              (coe v0) (coe v12) (coe v10) (coe v2) (coe v9)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                           (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
                              (coe
                                 MAlonzo.Code.Once.Type.C_μ'45'type_128
                                 (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v12)))
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_92
                    (coe
                       (\ v8 ->
                          coe
                            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_770
                            (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v7))
                            (coe
                               MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1002
                               (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v7))
                               (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                  (coe v7) (coe v6))
                               erased v8)))
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.d_force'7496'_14 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v6
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_in'45'ν'7496'_86
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_996
                          (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v7)) erased
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_728
                             (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v7))
                             (coe v4))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_120 v6 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_anaF'7496'_418
                       (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v9))
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_92
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_728
                                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v9))
                                    (coe v11)))
                            (coe
                               d_eval'7472'_12 (coe v0) (coe v1)
                               (coe
                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v1))
                               (coe v8) (coe v10)))
                       v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v6 v7
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
             (coe (\ v8 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe
                MAlonzo.Code.Once.Res.C_returns_12
                (coe
                   MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_514
                   (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_622 (coe v2))
                   (coe du_const'45'val_26 (coe v0) (coe v6) (coe v7))))
      MAlonzo.Code.Once.IR.C_SigOp_130 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
             (coe
                MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D'7495'_696
                (coe v5) (coe v7)
                (coe
                   MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_622
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v5)))
                   (coe v4)))
             (coe
                MAlonzo.Code.Once.Res.du_mapRes_46
                (coe
                   (\ v8 ->
                      MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_514
                        (coe v6) (coe v8)))
                (coe
                   MAlonzo.Code.Once.SigOp.Info.du_semM_220 v7 v0
                   (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_622
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v5)))
                      (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotTrace.in-val
d_in'45'val_16 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_in'45'val_16 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_936
      (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v0))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_110
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v0))
         (coe v1))
-- Once.Denotation.DenotTrace.out-μ-val
d_out'45'μ'45'val_20 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_out'45'μ'45'val_20 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_152
      (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v0))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_944
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v0))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v0)
            (coe v1))
         (coe v2))
-- Once.Denotation.DenotTrace.const-val
d_const'45'val_26 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 -> AgdaAny -> AgdaAny
d_const'45'val_26 v0 ~v1 v2 v3 = du_const'45'val_26 v0 v2 v3
du_const'45'val_26 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 -> AgdaAny -> AgdaAny
du_const'45'val_26 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_528
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20
             (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
             (coe v2)
      MAlonzo.Code.Once.IRTy.C_fits'45'float_530
        -> coe
             MAlonzo.Code.Once.Float.Decimal.d_round_174
             (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotTrace.cata-ev-algᴰ
d_cata'45'ev'45'alg'7472'_36 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_cata'45'ev'45'alg'7472'_36 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__70
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_196
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v1))
         (coe v6))
      (coe
         (\ v7 ->
            d_eval'7472'_12
              (coe v0)
              (coe
                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2)
                 (coe
                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v1) (coe v3)))
              (coe v3) (coe v4)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_770
                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v1))
                    (coe v7)))))
-- Once.Denotation.DenotTrace.liftFn
d_liftFn_260 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_liftFn_260 v0 v1 v2 v3 v4
  = coe
      d_eval'7472'_12 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v2)) (coe v3)
      (coe v4)
