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

module MAlonzo.Code.Once.Adequacy.RewritePreserves where

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
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.LiftSound
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.EvalRel
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.TraceTr
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Lang.FunctorMeaning
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.StreamInf
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Trace
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.RewritePreserves._.⟦_⟧F
d_'10214'_'10215'F_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_8 = erased
-- Once.Adequacy.RewritePreserves._._.E
d_E_30 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_E_30 v0 v1 ~v2 ~v3 v4 v5 = du_E_30 v0 v1 v4 v5
du_E_30 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_E_30 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
      (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.RewritePreserves._._.E′
d_E'8242'_36 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_E'8242'_36 v0 ~v1 v2 ~v3 v4 v5 = du_E'8242'_36 v0 v2 v4 v5
du_E'8242'_36 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_E'8242'_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
      (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.RewritePreserves._._.rewrite-rel
d_rewrite'45'rel_48 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_rewrite'45'rel_48 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_rw'45'at'45'rel_62 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Rewrite.d_try'45'lift_64 (coe v4)
         (coe v5) (coe v6))
      (coe v7) (coe v8)
-- Once.Adequacy.RewritePreserves._._.rw-at-rel
d_rw'45'at'45'rel_62 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_rw'45'at'45'rel_62 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11
  = du_rw'45'at'45'rel_62 v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
du_rw'45'at'45'rel_62 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_rw'45'at'45'rel_62 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
        -> coe
             seq (coe v11)
             (coe
                du_lifted_90 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5) (coe v6)
                (coe v8))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_walk'45'rel_74 v0 v1 v2 v3 v4 v5 v6 v8 v9 v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.RewritePreserves._._.walk-rel
d_walk'45'rel_74 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_walk'45'rel_74 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             (\ v10 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe v10))
      MAlonzo.Code.Once.IR.C__'8728'__28 v10 v12 v13
        -> coe
             (\ v14 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
                     (coe v1) (coe v4) (coe v10)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                           (coe v4) (coe v10) (coe v13)))
                     (coe v7))
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
                     (coe v2) (coe v4) (coe v10) (coe v13) (coe v8))
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
                     (coe v1) (coe v10) (coe v5)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                           (coe v10) (coe v5) (coe v12))))
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
                     (coe v2) (coe v10) (coe v5) (coe v12))
                  (coe d_rewrite'45'rel_48 v0 v1 v2 v3 v4 v10 v13 v7 v8 v14)
                  (coe
                     d_rewrite'45'rel_48 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                     (coe v5) (coe v12)))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v14 v15
               -> coe
                    (\ v16 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                         (coe
                            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
                            (coe v1) (coe v4) (coe v14)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                                  (coe v4) (coe v14) (coe v12)))
                            (coe v7))
                         (coe
                            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
                            (coe v2) (coe v4) (coe v14) (coe v12) (coe v8))
                         (coe
                            (\ v17 ->
                               coe
                                 MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                 (coe
                                    MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                    (coe v0) (coe v1) (coe v4) (coe v15)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                                          (coe v4) (coe v15) (coe v13)))
                                    (coe v7))
                                 (coe
                                    (\ v18 ->
                                       coe
                                         MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                            (coe v18))))))
                         (coe
                            (\ v17 ->
                               coe
                                 MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                 (coe
                                    MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                    (coe v0) (coe v2) (coe v4) (coe v15) (coe v13) (coe v8))
                                 (coe
                                    (\ v18 ->
                                       coe
                                         MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                            (coe v18))))))
                         (coe d_rewrite'45'rel_48 v0 v1 v2 v3 v4 v14 v12 v7 v8 v16)
                         (coe
                            (\ v17 v18 v19 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                 (coe
                                    MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                    (coe v0) (coe v1) (coe v4) (coe v15)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                                          (coe v4) (coe v15) (coe v13)))
                                    (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                    (coe v0) (coe v2) (coe v4) (coe v15) (coe v13) (coe v8))
                                 (coe
                                    (\ v20 ->
                                       coe
                                         MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                            (coe v20))))
                                 (coe
                                    (\ v20 ->
                                       coe
                                         MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                                            (coe v20))))
                                 (coe d_rewrite'45'rel_48 v0 v1 v2 v3 v4 v15 v13 v7 v8 v16)
                                 (coe
                                    (\ v20 v21 v22 ->
                                       coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v19)
                                            (coe v22)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             (\ v11 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v11)))
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             (\ v11 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v11)))
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             (\ v11 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe v11))
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             (\ v11 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe v11))
      MAlonzo.Code.Once.IR.C_case_68 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v14 v15
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
                      -> case coe v8 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                             -> coe
                                  (\ v18 ->
                                     coe d_rewrite'45'rel_48 v0 v1 v2 v3 v14 v5 v12 v16 v17 v18)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                             -> coe (\ v18 -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                      -> case coe v8 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                             -> coe (\ v18 -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                             -> coe
                                  (\ v18 ->
                                     coe d_rewrite'45'rel_48 v0 v1 v2 v3 v15 v5 v13 v16 v17 v18)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             (\ v10 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.IR.C_curry_84 v12
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v13 v14
               -> coe
                    (\ v15 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                         (coe
                            (\ v16 v17 v18 ->
                               coe
                                 d_rewrite'45'rel_48 v0 v1 v2 v3
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v4) (coe v13)) v14 v12
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v16))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) (coe v17))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                    (coe v18)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe
             (\ v11 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v11
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7))
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8))
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v11)))
      MAlonzo.Code.Once.IR.C_In_94 v10
        -> coe
             (\ v11 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  erased)
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v10
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'8315''185''45'rel_1188
                            (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                            (coe
                               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                               (coe v10))
                            (coe
                               MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478
                               (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                               (coe
                                  MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                  (coe v10))
                               (coe MAlonzo.Code.Once.Lang.Polynomial.d_outS_90 (coe v7)))
                            (coe
                               MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478
                               (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                               (coe
                                  MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                  (coe v10))
                               (coe MAlonzo.Code.Once.Lang.Polynomial.d_outS_90 (coe v7)))
                            (coe
                               du_frefl_288
                               (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                               (coe
                                  MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                  (coe v10))
                               (coe
                                  MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                  (coe
                                     MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                     (coe v10))
                                  (coe MAlonzo.Code.Once.Lang.Polynomial.d_outS_90 (coe v7))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v10 v13
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v14 v15
               -> case coe v15 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v16
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                    -> coe
                                         (\ v21 ->
                                            case coe v21 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                -> coe
                                                     MAlonzo.Code.Once.Denotation.ValueRel.du_sem'45'cata'45'rel_1512
                                                     (coe
                                                        MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                        (coe v16))
                                                     (coe
                                                        MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                        (coe v16) (coe v10))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.DenotTrace.d_cata'45'ev'45'alg'7472'_130
                                                        (coe v0) (coe v1) (coe v16) (coe v14)
                                                        (coe v5) (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                 (coe v14)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                    (coe v16) (coe v5)))
                                                              (coe v5) (coe v13)))
                                                        (coe v17))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.DenotTrace.d_cata'45'ev'45'alg'7472'_130
                                                        (coe v0) (coe v2) (coe v16) (coe v14)
                                                        (coe v5) (coe v10) (coe v13) (coe v19))
                                                     (coe
                                                        du_alg'45'step_348 (coe v0) (coe v1)
                                                        (coe v2) (coe v3) (coe v5) (coe v16)
                                                        (coe v10) (coe v14) (coe v13) (coe v17)
                                                        (coe v19) (coe v22))
                                                     (coe v18)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v10
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                         (coe MAlonzo.Code.Once.Lang.StreamInf.d_force'7477'_20 (coe v7))
                         (coe MAlonzo.Code.Once.Lang.StreamInf.d_force'7477'_20 (coe v8))
                         (coe
                            (\ v13 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                                 (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                    (coe v10))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
                                    (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                    (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                       (coe v11) (coe v10))
                                    erased v13)))
                         (coe
                            (\ v13 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                                 (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                    (coe v10))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
                                    (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                    (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                       (coe v11) (coe v10))
                                    erased v13)))
                         (coe MAlonzo.Code.Once.Denotation.ValueRel.d_forceR_32 (coe v12))
                         (coe
                            (\ v13 v14 v15 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'8315''185''45'rel_1188
                                 (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                    (coe v10))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478
                                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                    (coe
                                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                       (coe v10))
                                    (coe v13))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478
                                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                    (coe
                                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                       (coe v10))
                                    (coe v14))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.ValueRel.du_cμout'45'rel_1284
                                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                    (coe
                                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                       (coe v10))
                                    (coe v13) (coe v14)
                                    (coe
                                       MAlonzo.Code.Once.Denotation.ValueRel.du_layer'8594'srel_1530
                                       (coe
                                          MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11)))
                                       (coe v13) (coe v14) (coe v15))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v10
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueRel.d_in'45'rel_1616
                            (coe
                               MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56
                               (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11)))
                            (coe
                               MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
                               (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11)) erased
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                  (coe
                                     MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                     (coe v10))
                                  (coe v7)))
                            (coe
                               MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
                               (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11)) erased
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                  (coe
                                     MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                     (coe v10))
                                  (coe v8)))
                            (coe
                               MAlonzo.Code.Once.Denotation.ValueRel.du_cμin'45'rel_1246
                               (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                  (coe
                                     MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                     (coe v10))
                                  (coe v7))
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                  (coe
                                     MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                     (coe v10))
                                  (coe v8))
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'45'rel_1112
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v11))
                                  (coe
                                     MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                                     (coe v10))
                                  (coe v7) (coe v8) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_122 v10 v13
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v16
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                    -> coe
                                         (\ v21 ->
                                            case coe v21 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                -> coe
                                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.ValueRel.du_ana'7477''45'rel_1422
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                              (coe v16)))
                                                        (coe
                                                           (\ v24 ->
                                                              coe
                                                                MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
                                                                   (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                      (coe v16))
                                                                   erased)
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                                                                   (coe
                                                                      (\ v25 ->
                                                                         coe
                                                                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                              (coe v16))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                                              (coe v16) (coe v10))
                                                                           (coe v25)))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                                                      (coe v0) (coe v1) (coe v4)
                                                                      (coe
                                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                         (coe v16) (coe v15))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                                                                            (coe v4)
                                                                            (coe
                                                                               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                               (coe v16) (coe v15))
                                                                            (coe v13)))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v17) (coe v24))))))
                                                        (coe
                                                           (\ v24 ->
                                                              coe
                                                                MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
                                                                   (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                      (coe v16))
                                                                   erased)
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                                                                   (coe
                                                                      (\ v25 ->
                                                                         coe
                                                                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                              (coe v16))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                                              (coe v16) (coe v10))
                                                                           (coe v25)))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                                                      (coe v0) (coe v2) (coe v4)
                                                                      (coe
                                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                         (coe v16) (coe v15))
                                                                      (coe v13)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v19) (coe v24))))))
                                                        (coe
                                                           (\ v24 v25 v26 ->
                                                              coe
                                                                MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                                                                   (coe
                                                                      (\ v27 ->
                                                                         coe
                                                                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                              (coe v16))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                                              (coe v16) (coe v10))
                                                                           (coe v27)))
                                                                   (coe
                                                                      du_E_30 v0 v1 v4
                                                                      (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                         (coe v16) (coe v15))
                                                                      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                                                                            (coe v4)
                                                                            (coe
                                                                               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                               (coe v16) (coe v15))
                                                                            (coe v13)))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v17) (coe v24))))
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                                                                   (coe
                                                                      (\ v27 ->
                                                                         coe
                                                                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                              (coe v16))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                                              (coe v16) (coe v10))
                                                                           (coe v27)))
                                                                   (coe
                                                                      du_E'8242'_36 v0 v2 v4
                                                                      (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                         (coe v16) (coe v15))
                                                                      v13
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v19) (coe v25))))
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436
                                                                   (coe
                                                                      MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                      (coe v16)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436
                                                                   (coe
                                                                      MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                      (coe v16)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                                                   (coe
                                                                      du_E_30 v0 v1 v4
                                                                      (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                         (coe v16) (coe v15))
                                                                      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                                                                            (coe v4)
                                                                            (coe
                                                                               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                               (coe v16) (coe v15))
                                                                            (coe v13)))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v17) (coe v24)))
                                                                   (coe
                                                                      du_E'8242'_36 v0 v2 v4
                                                                      (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                         (coe v16) (coe v15))
                                                                      v13
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v19) (coe v25)))
                                                                   (coe
                                                                      (\ v27 ->
                                                                         coe
                                                                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                              (coe v16))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                                              (coe v16) (coe v10))
                                                                           (coe v27)))
                                                                   (coe
                                                                      (\ v27 ->
                                                                         coe
                                                                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                              (coe v16))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                                              (coe v16) (coe v10))
                                                                           (coe v27)))
                                                                   (coe
                                                                      d_rewrite'45'rel_48 v0 v1 v2
                                                                      v3 v4
                                                                      (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                         (coe v16) (coe v15))
                                                                      v13
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v17) (coe v24))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v19) (coe v25))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v22) (coe v26)))
                                                                   (coe
                                                                      (\ v27 v28 v29 ->
                                                                         coe
                                                                           MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'45'rel_1112
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                              (coe v16))
                                                                           (coe
                                                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                                              (coe v16) (coe v10))
                                                                           (coe v27) (coe v28)
                                                                           (coe v29))))
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.ValueRel.du_cμin'45'rel_1246
                                                                   (coe
                                                                      MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                                      (coe v16)))))
                                                        (coe v18) (coe v20) (coe v23))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v12
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v13 v14
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                             -> coe
                                  (\ v19 ->
                                     case coe v19 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                         -> coe
                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'iter'8734'_622
                                              (coe
                                                 (\ v22 ->
                                                    coe
                                                      du_E_30 v0 v1 v4
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v5)
                                                         (coe v14))
                                                      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                         (coe
                                                            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                                                            (coe v4)
                                                            (coe
                                                               MAlonzo.Code.Once.IRTy.C__'43'__22
                                                               (coe v5) (coe v14))
                                                            (coe v12)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v15) (coe v22))))
                                              (coe
                                                 (\ v22 ->
                                                    coe
                                                      du_E'8242'_36 v0 v2 v4
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v5)
                                                         (coe v14))
                                                      v12
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v17) (coe v22))))
                                              (coe (\ v22 v23 v24 -> v24))
                                              (coe
                                                 (\ v22 v23 v24 ->
                                                    coe
                                                      d_rewrite'45'rel_48 v0 v1 v2 v3 v4
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v5)
                                                         (coe v14))
                                                      v12
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v15) (coe v22))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v17) (coe v23))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v20) (coe v24))))
                                              (coe v16) (coe v18) (coe v21)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_134 v10 v11
        -> coe
             seq (coe v10)
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                     erased))
      MAlonzo.Code.Once.IR.C_SigOp_140 v9 v10 v11
        -> coe
             (\ v12 ->
                coe
                  du_bare'45'rel_446 (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
                  (coe v11) (coe v7)
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.Rewrite.d_try'45'lift_64
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v9))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v10))
                     (coe
                        MAlonzo.Code.Once.IR.C__'8728'__28
                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v9)) v6
                        (coe MAlonzo.Code.Once.IR.C_id_20))))
      MAlonzo.Code.Once.IR.C_Call_146 v11
        -> coe
             (\ v12 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v3 v11 v4 v5 v7 v8 v12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.RewritePreserves._._.lifted
d_lifted_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_lifted_90 v0 v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_lifted_90 v0 v1 v2 v4 v5 v6 v10
du_lifted_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_lifted_90 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Once.Adequacy.LiftSound.du_lift'45'now_2884 (coe v0)
              (coe v2) (coe v3) (coe v4) (coe v5) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> let v12 = coe v11 v1 v6 in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> coe
                                 seq (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Denotation.EvalRel.du_RelS'45'now_246
                                    (coe
                                       MAlonzo.Code.Once.Denotation.EvalRel.d_base'45'reflI_90
                                       (coe v4) (coe v10) (coe v13)))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.RewritePreserves._._._.frefl
d_frefl_288 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueRel.T_FRel_216
d_frefl_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_frefl_288 v9 v10 v11
du_frefl_288 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueRel.T_FRel_216
du_frefl_288 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'K_52 v4
        -> coe MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'K_228
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Id_54
        -> coe MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'Id_234 erased
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'inl_244
                           (coe du_frefl_288 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'inr_254
                           (coe du_frefl_288 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'pair_268
                           (coe du_frefl_288 (coe v7) (coe v5) (coe v9))
                           (coe du_frefl_288 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.RewritePreserves._._._.alg-step
d_alg'45'step_348 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_FRel_216 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_alg'45'step_348 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11 v12 v13
                  v14 v15
  = du_alg'45'step_348
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11 v12 v13 v14 v15
du_alg'45'step_348 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_FRel_216 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_alg'45'step_348 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du_seqF'8734'_370
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v5))
         (coe v12))
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du_seqF'8734'_370
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v5))
         (coe v13))
      (coe
         (\ v15 ->
            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v7)
                 (coe
                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v5) (coe v4)))
              (coe v4)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v7)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v5) (coe v4)))
                    (coe v4) (coe v8)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v5))
                    (coe
                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v5)
                       (coe v6))
                    (coe v15)))))
      (coe
         (\ v15 ->
            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
              (coe v0) (coe v2)
              (coe
                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v7)
                 (coe
                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v5) (coe v4)))
              (coe v4) (coe v8)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v5))
                    (coe
                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v5)
                       (coe v6))
                    (coe v15)))))
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_seqF'8734''45'rel_1058
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v5))
         (coe v12) (coe v13) (coe v14))
      (coe
         (\ v15 v16 v17 ->
            coe
              d_rewrite'45'rel_48 v0 v1 v2 v3
              (coe
                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v7)
                 (coe
                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v5) (coe v4)))
              v4 v8
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v5))
                    (coe
                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v5)
                       (coe v6))
                    (coe v15)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v5))
                    (coe
                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v5)
                       (coe v6))
                    (coe v16)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'8315''185''45'rel_1188
                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v5))
                    (coe
                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v5)
                       (coe v6))
                    (coe v15) (coe v16) (coe v17)))))
-- Once.Adequacy.RewritePreserves._._._.bare-rel
d_bare'45'rel_446 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_bare'45'rel_446 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 v10 ~v11
  = du_bare'45'rel_446 v0 v1 v2 v4 v5 v6 v7 v10
du_bare'45'rel_446 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_bare'45'rel_446 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             seq (coe v8)
             (let v9
                    = coe
                        MAlonzo.Code.Once.Adequacy.LiftSound.du_lift'45'now_2884 (coe v0)
                        (coe v2) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
                        (coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                           (coe MAlonzo.Code.Once.IR.C_SigOp_140 (coe v3) (coe v4) (coe v5))
                           (coe MAlonzo.Code.Once.IR.C_id_20)) in
              coe
                (case coe v9 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                     -> case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> let v14 = coe v13 v1 v6 in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                      -> coe
                                           seq (coe v16)
                                           (coe
                                              MAlonzo.Code.Once.Denotation.EvalRel.du_RelS'45'now_246
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.EvalRel.d_base'45'reflI_90
                                                 (coe
                                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                    (coe v4))
                                                 (coe v12) (coe v15)))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Denotation.EvalRel.du_sigop'45'rel_360 (coe v0)
             (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.RewritePreserves._.table-rel
d_table'45'rel_528 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_table'45'rel_528 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_calls'45'rel_542 (coe v0) (coe v1) (coe v2)) erased
-- Once.Adequacy.RewritePreserves._.calls-rel
d_calls'45'rel_542 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_calls'45'rel_542 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'embed_764
             (coe MAlonzo.Code.Once.Lang.Trace.du_unlinkedT_228)
             (coe MAlonzo.Code.Once.Lang.Trace.du_unlinkedT_228)
             (coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'halt_572)
      (:) v9 v10
        -> coe
             du_at_600 (coe v0) (coe v1) (coe v9) (coe v10) (coe v3) (coe v4)
             (coe v5)
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
                (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v9))
                (coe v3))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__196
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v9))
                (coe v4))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__196
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v9))
                (coe v5))
             (coe v6) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.RewritePreserves._._.hit
d_hit_586 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_hit_586 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          v14 v15 v16
  = du_hit_586 v0 v1 v2 v3 v14 v15 v16
du_hit_586 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_hit_586 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_rewrite'45'rel_48 v0
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
            (coe v1)
            (coe MAlonzo.Code.Once.Compile.d_rewrite'45'table_888 (coe v3)))
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
            (coe
               MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
               (coe v1)
               (coe MAlonzo.Code.Once.Compile.d_rewrite'45'table_888 (coe v3)))))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
            (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
            (coe
               MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
               (coe v1) (coe v3))))
      (d_table'45'rel_528 (coe v0) (coe v1) (coe v3))
      (MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
      (MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
      (MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)) v4 v5 v6
-- Once.Adequacy.RewritePreserves._._.at
d_at_600 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_at_600 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10 v11 v12 v13 v14 v15
  = du_at_600 v0 v1 v2 v3 v4 v5 v6 v10 v11 v12 v13 v14 v15
du_at_600 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_at_600 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
        -> if coe v13
             then coe
                    seq (coe v14)
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                         -> if coe v15
                              then coe
                                     seq (coe v16)
                                     (case coe v9 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                          -> if coe v17
                                               then coe
                                                      seq (coe v18)
                                                      (coe
                                                         du_hit_586 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v10) (coe v11) (coe v12))
                                               else coe
                                                      seq (coe v18)
                                                      (coe
                                                         d_calls'45'rel_542 (coe v0) (coe v1)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v10) (coe v11) (coe v12))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v16)
                                     (coe
                                        d_calls'45'rel_542 (coe v0) (coe v1) (coe v3) (coe v4)
                                        (coe v5) (coe v6) (coe v10) (coe v11) (coe v12))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v14)
                    (coe
                       d_calls'45'rel_542 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
                       (coe v6) (coe v10) (coe v11) (coe v12))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.RewritePreserves._.program-rel
d_program'45'rel_616 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_program'45'rel_616 v0 v1 v2
  = coe
      d_rewrite'45'rel_48 v0
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
            (coe v1)
            (coe
               MAlonzo.Code.Once.Compile.d_rewrite'45'table_888
               (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v2))))
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
            (coe
               MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
               (coe v1)
               (coe
                  MAlonzo.Code.Once.Compile.d_rewrite'45'table_888
                  (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v2))))))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
            (coe v1)
            (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v2)))
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
            (coe
               MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
               (coe v1)
               (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v2)))))
      (d_table'45'rel_528
         (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v2)))
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (MAlonzo.Code.Once.Denotation.Program.d_main_394 (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.RewritePreserves.rewrite-program-trace
d_rewrite'45'program'45'trace_626 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_rewrite'45'program'45'trace_626 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceTr.du_RelS'45'tr_568 (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.Denotation.Program.d_runIR_398 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262 (coe v1))
         (coe MAlonzo.Code.Once.Compile.d_rewrite'45'program_894 (coe v2)))
      (coe
         MAlonzo.Code.Once.Denotation.Program.d_runIR_398 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262 (coe v1))
         (coe v2))
