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

module MAlonzo.Code.Once.Denotation.TraceTr where

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
import qualified MAlonzo.Code.Once.Adequacy.MachineTrace
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Trace

-- Once.Denotation.TraceTr.V.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Denotation.TraceTr.V.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Denotation.TraceTr.V.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_246 v0 v2
-- Once.Denotation.TraceTr.V.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_288 v0
      v2
-- Once.Denotation.TraceTr.V.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Denotation.TraceTr.V.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Denotation.TraceTr.V.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.Denotation.TraceTr.V.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
-- Once.Denotation.TraceTr.V.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104
-- Once.Denotation.TraceTr.V.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_598
-- Once.Denotation.TraceTr.V.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_588
-- Once.Denotation.TraceTr.V.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_30 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518
-- Once.Denotation.TraceTr.V.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_526
-- Once.Denotation.TraceTr.V.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Denotation.TraceTr.V.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Denotation.TraceTr.V.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Denotation.TraceTr.V.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Denotation.TraceTr.V.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Denotation.TraceTr.V.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Denotation.TraceTr.V.⟦_⟧
d_'10214'_'10215'_46 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Denotation.TraceTr.V.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Denotation.TraceTr.V.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Denotation.TraceTr.V.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Denotation.TraceTr.V.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Denotation.TraceTr.endOf
d_endOf_58 ::
  () ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8
d_endOf_58 ~v0 v1 = du_endOf_58 v1
du_endOf_58 ::
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8
du_endOf_58 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Res.C_stopped_12
        -> coe MAlonzo.Code.Once.Spec.Trace.C_halted_14
      MAlonzo.Code.Once.Lang.Res.C_returns_14 v1
        -> coe
             MAlonzo.Code.Once.Spec.Trace.C_returned_12
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._.Conf
d_Conf_66 :: MAlonzo.Code.Once.Lang.Trace.T_Interp_182 -> () -> ()
d_Conf_66 = erased
-- Once.Denotation.TraceTr._.node
d_node_72 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_node_72 v0 ~v1 v2 v3 = du_node_72 v0 v2 v3
du_node_72 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_node_72 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v3
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe
                MAlonzo.Code.Once.Spec.Trace.C_returned_12
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v3 v4 v5
        -> coe
             du_answer_78 (coe v1) (coe v3) (coe v4) (coe v5)
             (coe
                MAlonzo.Code.Once.Lang.Trace.d_callAnswer_330 (coe v0) (coe v1)
                (coe v3) (coe v4))
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v3 v4
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   MAlonzo.Code.Once.Lang.Event.d_toEvent_164
                   (coe
                      MAlonzo.Code.Once.Lang.Trace.d_haltEvent_102 (coe v3) (coe v4))))
             (coe MAlonzo.Code.Once.Spec.Trace.C_halted_14)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._.answer
d_answer_78 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  Maybe AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_answer_78 ~v0 ~v1 v2 v3 v4 v5 v6 = du_answer_78 v2 v3 v4 v5 v6
du_answer_78 ::
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  Maybe AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_answer_78 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_emit_14
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   MAlonzo.Code.Once.Lang.Event.d_toEvent_164
                   (coe
                      MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v1) (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe
                         MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v1) (coe v2))))
                (coe v3 v5))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   MAlonzo.Code.Once.Lang.Event.d_toEvent_164
                   (coe
                      MAlonzo.Code.Once.Lang.Trace.d_haltEvent_102
                      (coe MAlonzo.Code.Once.Lang.Trace.d_unlinkedOp_224)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             (coe MAlonzo.Code.Once.Spec.Trace.C_halted_14)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._.δ∞
d_δ'8734'_82 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'8734'_82 v0 ~v1 v2 = du_δ'8734'_82 v0 v2
du_δ'8734'_82 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ'8734'_82 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             du_node_72 (coe v0) (coe v2)
             (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._.trT∞
d_trT'8734'_126 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_trT'8734'_126 v0 ~v1 v2 v3 = du_trT'8734'_126 v0 v2 v3
du_trT'8734'_126 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_trT'8734'_126 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.MachineTrace.du_trace_80
      (coe du_δ'8734'_82 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
-- Once.Denotation.TraceTr._.runTr
d_runTr_136 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_runTr_136 v0 ~v1 v2 v3 = du_runTr_136 v0 v2 v3
du_runTr_136 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_runTr_136 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.MachineTrace.d_listTr_20
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Lang.Event.d_toEvent_164)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v0) (coe v1)
               (coe v2))))
      (coe
         du_endOf_58
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v0) (coe v1)
               (coe v2))))
-- Once.Denotation.TraceTr._._._.Reaches
d_Reaches_154 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Denotation.TraceTr._._.reachC
d_reachC_186 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_reachC_186 v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 v9 v10 ~v11 v12
  = du_reachC_186 v0 v4 v6 v7 v8 v9 v10 v12
du_reachC_186 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  Maybe AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_reachC_186 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'emit_104
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe
                         MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v2) (coe v3))))
                (coe v4 v8))
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   MAlonzo.Code.Once.Lang.Event.d_toEvent_164
                   (coe
                      MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe MAlonzo.Code.Once.Lang.Event.d_toEvent_164)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v0)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                         (coe
                            MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                            (coe
                               MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v2) (coe v3))))
                      (coe v5 v8))))
             (coe
                du_RelT'8734''8242''45'reaches_194 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe
                         MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v2) (coe v3))))
                (coe v4 v8) (coe v5 v8) (coe v7 v8))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'stop_112
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._._.RelT∞′-reaches
d_RelT'8734''8242''45'reaches_194 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_RelT'8734''8242''45'reaches_194 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelT'8734''8242''45'reaches_194 v0 v4 v5 v6 v7
du_RelT'8734''8242''45'reaches_194 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_RelT'8734''8242''45'reaches_194 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518 v6 v9
        -> coe MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'stop_112
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'call_532 v8 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Trace.C_call_118 v12 v13 v14
               -> coe
                    du_reachC_186 (coe v0) (coe v1) (coe v12) (coe v13) (coe v8)
                    (coe v14)
                    (coe
                       MAlonzo.Code.Once.Lang.Trace.d_callAnswer_330 (coe v0) (coe v1)
                       (coe v12) (coe v13))
                    (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'halt_540
        -> coe MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'stop_112
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._._.RelT∞′-tr
d_RelT'8734''8242''45'tr_242 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_RelT'8734''8242''45'tr_242 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelT'8734''8242''45'tr_242 v0 v4 v5 v6 v7
du_RelT'8734''8242''45'tr_242 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_RelT'8734''8242''45'tr_242 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.MachineTrace.du_reaches'45''8776'_426
      (coe du_δ'8734'_82 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Lang.Event.d_toEvent_164)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v0) (coe v1)
               (coe v3))))
      (coe
         du_endOf_58
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v0) (coe v1)
               (coe v3))))
      (coe
         du_RelT'8734''8242''45'reaches_194 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4))
