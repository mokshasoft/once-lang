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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.FuelTrace
import qualified MAlonzo.Code.Once.Adequacy.MachineTrace
import qualified MAlonzo.Code.Once.Denotation.Approx
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Res
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Trace

-- Once.Denotation.TraceTr.V.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Denotation.TraceTr.V.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Denotation.TraceTr.V.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor_246 v0 v2
-- Once.Denotation.TraceTr.V.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor'8315''185'_288
      v0 v2
-- Once.Denotation.TraceTr.V.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Denotation.TraceTr.V.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Denotation.TraceTr.V.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_578
-- Once.Denotation.TraceTr.V.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_584
-- Once.Denotation.TraceTr.V.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Internal.Value.du_erase'7501'_104
-- Once.Denotation.TraceTr.V.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoIn_598
-- Once.Denotation.TraceTr.V.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoOut_588
-- Once.Denotation.TraceTr.V.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_μS_82
d_sem'45'In_30
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'In_518
-- Once.Denotation.TraceTr.V.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'Out_526
-- Once.Denotation.TraceTr.V.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Denotation.TraceTr.V.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Denotation.TraceTr.V.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Denotation.TraceTr.V.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Denotation.TraceTr.V.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Denotation.TraceTr.V.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Denotation.TraceTr.V.⟦_⟧
d_'10214'_'10215'_46 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Denotation.TraceTr.V.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Denotation.TraceTr.V.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Denotation.TraceTr.V.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Denotation.TraceTr.V.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Denotation.TraceTr.endOf
d_endOf_58 ::
  () ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8
d_endOf_58 ~v0 v1 = du_endOf_58 v1
du_endOf_58 ::
  MAlonzo.Code.Once.Internal.Res.T_Res_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8
du_endOf_58 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Res.C_stopped_12
        -> coe MAlonzo.Code.Once.Spec.Trace.C_halted_14
      MAlonzo.Code.Once.Internal.Res.C_returns_14 v1
        -> coe
             MAlonzo.Code.Once.Spec.Trace.C_returned_12
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._.Conf
d_Conf_66 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 -> () -> ()
d_Conf_66 = erased
-- Once.Denotation.TraceTr._.answer
d_answer_74 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  Maybe AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_answer_74 ~v0 ~v1 v2 v3 v4 v5 v6 = du_answer_74 v2 v3 v4 v5 v6
du_answer_74 ::
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  Maybe AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_answer_74 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_emit_14
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   MAlonzo.Code.Once.Internal.Event.d_toEvent_164
                   (coe
                      MAlonzo.Code.Once.Internal.Trace.d_callEvent_94 (coe v1)
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe
                         MAlonzo.Code.Once.Internal.Trace.d_callEvent_94 (coe v1)
                         (coe v2))))
                (coe v3 v5))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   MAlonzo.Code.Once.Internal.Event.d_toEvent_164
                   (coe
                      MAlonzo.Code.Once.Internal.Trace.d_haltEvent_102
                      (coe MAlonzo.Code.Once.Internal.Trace.d_unlinkedOp_224)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             (coe MAlonzo.Code.Once.Spec.Trace.C_halted_14)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._.δ∞
d_δ'8734'_78 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'8734'_78 v0 ~v1 v2 = du_δ'8734'_78 v0 v2
du_δ'8734'_78 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ'8734'_78 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v4
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
                      -> coe
                           MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                           (coe
                              MAlonzo.Code.Once.Spec.Trace.C_returned_12
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                      -> coe
                           MAlonzo.Code.Once.Adequacy.MachineTrace.C_silent_12
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                              (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v5)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v4 v5 v6
               -> coe
                    du_answer_74 (coe v2) (coe v4) (coe v5) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Internal.Trace.d_callAnswer_330 (coe v0) (coe v2)
                       (coe v4) (coe v5))
             MAlonzo.Code.Once.Internal.Trace.C_halt_122 v4 v5
               -> coe
                    MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
                    (coe
                       MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                       (coe
                          MAlonzo.Code.Once.Internal.Event.d_toEvent_164
                          (coe
                             MAlonzo.Code.Once.Internal.Trace.d_haltEvent_102 (coe v4)
                             (coe v5))))
                    (coe MAlonzo.Code.Once.Spec.Trace.C_halted_14)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._.trT∞
d_trT'8734'_122 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_trT'8734'_122 v0 ~v1 v2 v3 = du_trT'8734'_122 v0 v2 v3
du_trT'8734'_122 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_trT'8734'_122 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.MachineTrace.du_trace_80
      (coe du_δ'8734'_78 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2)))
-- Once.Denotation.TraceTr._.runTr
d_runTr_132 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_runTr_132 v0 ~v1 v2 v3 = du_runTr_132 v0 v2 v3
du_runTr_132 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_runTr_132 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.MachineTrace.d_listTr_20
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Internal.Event.d_toEvent_164)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Internal.Trace.du_run_342 (coe v0) (coe v1)
               (coe v2))))
      (coe
         du_endOf_58
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.Internal.Trace.du_run_342 (coe v0) (coe v1)
               (coe v2))))
-- Once.Denotation.TraceTr._._._.Reaches
d_Reaches_150 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Denotation.TraceTr._._.reachC
d_reachC_182 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelB_140) ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_reachC_182 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 ~v10 v11
  = du_reachC_182 v0 v4 v5 v6 v7 v8 v9 v11
du_reachC_182 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  Maybe AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelB_140) ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_reachC_182 v0 v1 v2 v3 v4 v5 v6 v7
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
                         MAlonzo.Code.Once.Internal.Trace.d_callEvent_94 (coe v2)
                         (coe v3))))
                (coe v4 v8))
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   MAlonzo.Code.Once.Internal.Event.d_toEvent_164
                   (coe
                      MAlonzo.Code.Once.Internal.Trace.d_callEvent_94 (coe v2)
                      (coe v3))))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe MAlonzo.Code.Once.Internal.Event.d_toEvent_164)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Internal.Trace.du_run_342 (coe v0)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                         (coe
                            MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                            (coe
                               MAlonzo.Code.Once.Internal.Trace.d_callEvent_94 (coe v2)
                               (coe v3))))
                      (coe v5 v8))))
             (coe
                du_RelB'45'reaches_190 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe
                         MAlonzo.Code.Once.Internal.Trace.d_callEvent_94 (coe v2)
                         (coe v3))))
                (coe v4 v8) (coe v5 v8) (coe v7 v8))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'stop_112
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._._.RelB-reaches
d_RelB'45'reaches_190 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelB_140 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_RelB'45'reaches_190 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelB'45'reaches_190 v0 v4 v5 v6 v7
du_RelB'45'reaches_190 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelB_140 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_RelB'45'reaches_190 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_b'45'ret_152 v7
        -> coe MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'stop_112
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_b'45'tau_158 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'silent_92
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                              (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v9)))
                           (coe
                              du_RelB'45'reaches_190 (coe v0) (coe v1)
                              (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v9))
                              (coe v3) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_b'45'call_170 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v10 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
                      -> coe
                           du_reachC_182 (coe v0) (coe v1) (coe v10) (coe v11) (coe v12)
                           (coe v15)
                           (coe
                              MAlonzo.Code.Once.Internal.Trace.d_callAnswer_330 (coe v0) (coe v1)
                              (coe v10) (coe v11))
                           (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_b'45'halt_176
        -> coe MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'stop_112
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._._.RelT∞′-tr
d_RelT'8734''8242''45'tr_236 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_188 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_RelT'8734''8242''45'tr_236 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelT'8734''8242''45'tr_236 v0 v4 v5 v6 v7
du_RelT'8734''8242''45'tr_236 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_188 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_RelT'8734''8242''45'tr_236 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.MachineTrace.du_reaches'45''8776'_426
      (coe du_δ'8734'_78 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2)))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Internal.Event.d_toEvent_164)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Internal.Trace.du_run_342 (coe v0) (coe v1)
               (coe v3))))
      (coe
         du_endOf_58
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.Internal.Trace.du_run_342 (coe v0) (coe v1)
               (coe v3))))
      (coe
         du_RelB'45'reaches_190 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe v3)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_block_202
            (coe v4)))
-- Once.Denotation.TraceTr.obsAp
d_obsAp_244 ::
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_obsAp_244 ~v0 v1 = du_obsAp_244 v1
du_obsAp_244 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_obsAp_244 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Internal.Event.d_toEvent_164)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         MAlonzo.Code.Once.Denotation.Approx.du_endAp_814
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
-- Once.Denotation.TraceTr._._.runN
d_runN_258 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runN_258 v0 ~v1 = du_runN_258 v0
du_runN_258 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runN_258 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FuelTrace.du_runN_262
      (coe du_δ'8734'_78 (coe v0))
-- Once.Denotation.TraceTr._.approx-runB
d_approx'45'runB_268 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_approx'45'runB_268 v0 ~v1 v2 v3 v4
  = du_approx'45'runB_268 v0 v2 v3 v4
du_approx'45'runB_268 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_approx'45'runB_268 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> case coe v1 of
                    0 -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                              (coe (\ v6 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
                    _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
                         coe
                           (let v7
                                  = coe
                                      du_approx'45'runB_268 (coe v0) (coe v6) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Iterative.d_force_64
                                         (coe v5)) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe addInt (coe (1 :: Integer)) (coe v8))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v10)
                                                  (coe
                                                     (\ v12 ->
                                                        coe
                                                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                          (coe v11 v12))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v4 v5 v6
        -> let v7
                 = coe
                     du_approx'45'call_288 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                     (coe v6)
                     (coe
                        MAlonzo.Code.Once.Internal.Trace.d_callAnswer_330 (coe v0) (coe v2)
                        (coe v4) (coe v5)) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> coe
                       seq (coe v9)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._.approx-call
d_approx'45'call_288 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_approx'45'call_288 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_approx'45'call_288 v0 v2 v3 v4 v5 v6 v7
du_approx'45'call_288 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_approx'45'call_288 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> let v8
                 = coe
                     du_approx'45'runB_268 (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                        (coe
                           MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                           (coe
                              MAlonzo.Code.Once.Internal.Trace.d_callEvent_94 (coe v3)
                              (coe v4))))
                     (coe v5 v7) in
           coe
             (case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe (\ v13 -> coe v12 v13)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceTr._.approx-run
d_approx'45'run_420 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_approx'45'run_420 v0 ~v1 v2 v3 v4
  = du_approx'45'run_420 v0 v2 v3 v4
du_approx'45'run_420 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_approx'45'run_420 v0 v1 v2 v3
  = coe
      du_approx'45'runB_268 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3))
-- Once.Denotation.TraceTr._.FX.runN
d_runN_454 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runN_454 v0 ~v1 ~v2 ~v3 = du_runN_454 v0
du_runN_454 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runN_454 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FuelTrace.du_runN_262
      (coe du_δ'8734'_78 (coe v0))
-- Once.Denotation.TraceTr._.FX.runS
d_runS_458 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runS_458 v0 ~v1 ~v2 ~v3 = du_runS_458 v0
du_runS_458 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runS_458 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FuelTrace.du_runS_264
      (coe du_δ'8734'_78 (coe v0))
-- Once.Denotation.TraceTr._.FY.runN
d_runN_476 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runN_476 v0 ~v1 ~v2 ~v3 = du_runN_476 v0
du_runN_476 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runN_476 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FuelTrace.du_runN_262
      (coe du_δ'8734'_78 (coe v0))
-- Once.Denotation.TraceTr._.FY.runS
d_runS_480 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runS_480 v0 ~v1 ~v2 ~v3 = du_runS_480 v0
du_runS_480 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runS_480 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FuelTrace.du_runS_264
      (coe du_δ'8734'_78 (coe v0))
-- Once.Denotation.TraceTr._.RelSB-runN
d_RelSB'45'runN_492 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RelSB'45'runN_492 = erased
-- Once.Denotation.TraceTr._.RelSB-ans
d_RelSB'45'ans_510 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RelSB'45'ans_510 = erased
-- Once.Denotation.TraceTr._.RelS-tr
d_RelS'45'tr_568 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_RelS'45'tr_568 v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_RelS'45'tr_568 v0 v4 v5 v6
du_RelS'45'tr_568 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_RelS'45'tr_568 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.FuelTrace.du_agree'45''8776'_1164
      (coe du_δ'8734'_78 (coe v0)) (coe du_δ'8734'_78 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3)))
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe
                       (\ v5 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v4))
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                               (coe v4))))))))
