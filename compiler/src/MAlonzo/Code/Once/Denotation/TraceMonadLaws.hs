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

module MAlonzo.Code.Once.Denotation.TraceMonadLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value

-- Once.Denotation.TraceMonadLaws.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Denotation.TraceMonadLaws.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Denotation.TraceMonadLaws.M.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_246 v0 v2
-- Once.Denotation.TraceMonadLaws.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_288 v0
      v2
-- Once.Denotation.TraceMonadLaws.M.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Denotation.TraceMonadLaws.M.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Denotation.TraceMonadLaws.M.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.Denotation.TraceMonadLaws.M.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
-- Once.Denotation.TraceMonadLaws.M.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104
-- Once.Denotation.TraceMonadLaws.M.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_598
-- Once.Denotation.TraceMonadLaws.M.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_588
-- Once.Denotation.TraceMonadLaws.M.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_30 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518
-- Once.Denotation.TraceMonadLaws.M.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_526
-- Once.Denotation.TraceMonadLaws.M.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Denotation.TraceMonadLaws.M.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Denotation.TraceMonadLaws.M.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Denotation.TraceMonadLaws.M.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Denotation.TraceMonadLaws.M.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Denotation.TraceMonadLaws.M.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Denotation.TraceMonadLaws.M.⟦_⟧
d_'10214'_'10215'_46 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Denotation.TraceMonadLaws.M.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Denotation.TraceMonadLaws.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Denotation.TraceMonadLaws.M.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Denotation.TraceMonadLaws.M.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Denotation.TraceMonadLaws.>>=T-identityˡ
d_'62''62''61'T'45'identity'737'_64 ::
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'identity'737'_64 = erased
-- Once.Denotation.TraceMonadLaws.>>=T-identityʳ
d_'62''62''61'T'45'identity'691'_74 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'identity'691'_74 = erased
-- Once.Denotation.TraceMonadLaws.>>=T-assoc
d_'62''62''61'T'45'assoc_104 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'assoc_104 = erased
-- Once.Denotation.TraceMonadLaws.>>=T-cong
d_'62''62''61'T'45'cong_144 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'cong_144 = erased
-- Once.Denotation.TraceMonadLaws.fmapT-id
d_fmapT'45'id_158 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapT'45'id_158 = erased
-- Once.Denotation.TraceMonadLaws.fmapT-∘
d_fmapT'45''8728'_174 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapT'45''8728'_174 = erased
-- Once.Denotation.TraceMonadLaws.fmapT-cong
d_fmapT'45'cong_194 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapT'45'cong_194 = erased
-- Once.Denotation.TraceMonadLaws.length-take-≤
d_length'45'take'45''8804'_206 ::
  Integer ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'take'45''8804'_206 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                [] -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                (:) v3 v4
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (d_length'45'take'45''8804'_206 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonadLaws.take-sat
d_take'45'sat_216 ::
  Integer ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'sat_216 = erased
-- Once.Denotation.TraceMonadLaws.take-coh
d_take'45'coh_234 ::
  Integer ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_take'45'coh_234 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             []
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
             (:) v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v2)) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                []
                  -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
                (:) v3 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_take'45'coh_234 (coe v2) (coe v4)))
                       erased
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonadLaws.take-pf
d_take'45'pf_254 ::
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_PrefixFamily_476
d_take'45'pf_254 v0
  = coe
      MAlonzo.Code.Once.Lang.Trace.C_prefixFamily_492
      (\ v1 -> d_length'45'take'45''8804'_206 (coe v1) (coe v0))
      (\ v1 -> d_take'45'coh_234 (coe v1) (coe v0))
-- Once.Denotation.TraceMonadLaws.projTrace-pf
d_projTrace'45'pf_270 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_PrefixFamily_476
d_projTrace'45'pf_270 ~v0 v1 v2 = du_projTrace'45'pf_270 v1 v2
du_projTrace'45'pf_270 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_PrefixFamily_476
du_projTrace'45'pf_270 v0 v1
  = coe
      d_take'45'pf_254
      (coe MAlonzo.Code.Once.Lang.Trace.du_eventsT_438 (coe v0) (coe v1))
-- Once.Denotation.TraceMonadLaws.RelT′-bind
d_RelT'8242''45'bind_300 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_RelT'8242''45'bind_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10
                         v11
  = du_RelT'8242''45'bind_300 v6 v7 v10 v11
du_RelT'8242''45'bind_300 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelT'8242''45'bind_300 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v7
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Trace.C_ret_114 v8 -> coe v3 v7 v8 v6
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'call_566 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Trace.C_call_118 v9 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Trace.C_call_118 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Lang.Trace.C_rel'45'call_566
                           (\ v15 ->
                              coe
                                du_RelT'8242''45'bind_300 (coe v11 v15) (coe v14 v15) (coe v8 v15)
                                (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'halt_572
        -> coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'halt_572
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadLaws.RelT′-fmap
d_RelT'8242''45'fmap_350 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_RelT'8242''45'fmap_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
                         v11
  = du_RelT'8242''45'fmap_350 v8 v9 v10 v11
du_RelT'8242''45'fmap_350 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelT'8242''45'fmap_350 v0 v1 v2 v3
  = coe
      du_RelT'8242''45'bind_300 (coe v0) (coe v1) (coe v3)
      (coe
         (\ v4 v5 v6 ->
            coe
              MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 (coe v2 v4 v5 v6)))
-- Once.Denotation.TraceMonadLaws.RelT′-refl
d_RelT'8242''45'refl_374 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_RelT'8242''45'refl_374 ~v0 ~v1 v2 v3
  = du_RelT'8242''45'refl_374 v2 v3
du_RelT'8242''45'refl_374 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelT'8242''45'refl_374 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Trace.C_ret_114 v2
        -> coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 (coe v0 v2)
      MAlonzo.Code.Once.Lang.Trace.C_call_118 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Trace.C_rel'45'call_566
             (\ v5 -> coe du_RelT'8242''45'refl_374 (coe v0) (coe v4 v5))
      MAlonzo.Code.Once.Lang.Trace.C_halt_122 v2 v3
        -> coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'halt_572
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadLaws.RelT′-≡
d_RelT'8242''45''8801'_410 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RelT'8242''45''8801'_410 = erased
-- Once.Denotation.TraceMonadLaws.≡-RelT′
d_'8801''45'RelT'8242'_436 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_'8801''45'RelT'8242'_436 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_'8801''45'RelT'8242'_436 v3
du_'8801''45'RelT'8242'_436 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_'8801''45'RelT'8242'_436 v0 = coe du_to'45'fmap_452 (coe v0)
-- Once.Denotation.TraceMonadLaws._.to-fmap
d_to'45'fmap_452 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_to'45'fmap_452 ~v0 ~v1 ~v2 ~v3 v4 = du_to'45'fmap_452 v4
du_to'45'fmap_452 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_to'45'fmap_452 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Trace.C_ret_114 v1
        -> coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 erased
      MAlonzo.Code.Once.Lang.Trace.C_call_118 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Lang.Trace.C_rel'45'call_566
             (\ v4 -> coe du_to'45'fmap_452 (coe v3 v4))
      MAlonzo.Code.Once.Lang.Trace.C_halt_122 v1 v2
        -> coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'halt_572
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadLaws.RelT′-events
d_RelT'8242''45'events_482 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RelT'8242''45'events_482 = erased
-- Once.Denotation.TraceMonadLaws._.go
d_go_504 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_504 = erased
-- Once.Denotation.TraceMonadLaws.run-bind
d_run'45'bind_526 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'bind_526 = erased
-- Once.Denotation.TraceMonadLaws.run-bind-call
d_run'45'bind'45'call_548 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'bind'45'call_548 = erased
-- Once.Denotation.TraceMonadLaws.cons-then
d_cons'45'then_566 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cons'45'then_566 = erased
