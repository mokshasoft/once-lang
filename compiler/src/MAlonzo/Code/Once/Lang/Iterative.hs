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

module MAlonzo.Code.Once.Lang.Iterative where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value

-- Once.Lang.Iterative.V.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Lang.Iterative.V.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Lang.Iterative.V.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_246 v0 v2
-- Once.Lang.Iterative.V.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_288 v0
      v2
-- Once.Lang.Iterative.V.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Lang.Iterative.V.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Lang.Iterative.V.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.Lang.Iterative.V.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
-- Once.Lang.Iterative.V.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104
-- Once.Lang.Iterative.V.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_598
-- Once.Lang.Iterative.V.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_588
-- Once.Lang.Iterative.V.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_30 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518
-- Once.Lang.Iterative.V.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_526
-- Once.Lang.Iterative.V.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Lang.Iterative.V.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Lang.Iterative.V.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Lang.Iterative.V.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Lang.Iterative.V.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Lang.Iterative.V.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Lang.Iterative.V.⟦_⟧
d_'10214'_'10215'_46 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Lang.Iterative.V.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Lang.Iterative.V.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Lang.Iterative.V.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Lang.Iterative.V.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Lang.Iterative.T∞F
d_T'8734'F_60 a0 a1 = ()
data T_T'8734'F_60
  = C_ret'8734'_66 AgdaAny |
    C_call'8734'_70 MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 AgdaAny
                    (AgdaAny -> AgdaAny) |
    C_halt'8734'_74 MAlonzo.Code.Once.Lang.Trace.T_HaltOp_76 AgdaAny
-- Once.Lang.Iterative.T∞
d_T'8734'_78 a0 = ()
data T_T'8734'_78 = C_constructor_86 T_T'8734'F_60
-- Once.Lang.Iterative.T∞.force
d_force_84 :: T_T'8734'_78 -> T_T'8734'F_60
d_force_84 v0
  = case coe v0 of
      C_constructor_86 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Iterative.return∞
d_return'8734'_90 :: () -> AgdaAny -> T_T'8734'_78
d_return'8734'_90 ~v0 v1 = du_return'8734'_90 v1
du_return'8734'_90 :: AgdaAny -> T_T'8734'_78
du_return'8734'_90 v0
  = coe C_constructor_86 (coe C_ret'8734'_66 (coe v0))
-- Once.Lang.Iterative._>>=∞_
d__'62''62''61''8734'__98 ::
  () ->
  () -> T_T'8734'_78 -> (AgdaAny -> T_T'8734'_78) -> T_T'8734'_78
d__'62''62''61''8734'__98 ~v0 ~v1 v2 v3
  = du__'62''62''61''8734'__98 v2 v3
du__'62''62''61''8734'__98 ::
  T_T'8734'_78 -> (AgdaAny -> T_T'8734'_78) -> T_T'8734'_78
du__'62''62''61''8734'__98 v0 v1
  = coe
      C_constructor_86
      (coe du_bind'8734'F_104 (coe d_force_84 (coe v0)) (coe v1))
-- Once.Lang.Iterative.bind∞F
d_bind'8734'F_104 ::
  () ->
  () -> T_T'8734'F_60 -> (AgdaAny -> T_T'8734'_78) -> T_T'8734'F_60
d_bind'8734'F_104 ~v0 ~v1 v2 v3 = du_bind'8734'F_104 v2 v3
du_bind'8734'F_104 ::
  T_T'8734'F_60 -> (AgdaAny -> T_T'8734'_78) -> T_T'8734'F_60
du_bind'8734'F_104 v0 v1
  = case coe v0 of
      C_ret'8734'_66 v2 -> coe d_force_84 (coe v1 v2)
      C_call'8734'_70 v2 v3 v4
        -> coe
             C_call'8734'_70 (coe v2) (coe v3)
             (coe (\ v5 -> coe du__'62''62''61''8734'__98 (coe v4 v5) (coe v1)))
      C_halt'8734'_74 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Iterative.embed
d_embed_132 ::
  () -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> T_T'8734'_78
d_embed_132 ~v0 v1 = du_embed_132 v1
du_embed_132 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> T_T'8734'_78
du_embed_132 v0
  = coe
      C_constructor_86
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Trace.C_ret_114 v1
           -> coe C_ret'8734'_66 (coe v1)
         MAlonzo.Code.Once.Lang.Trace.C_call_118 v1 v2 v3
           -> coe
                C_call'8734'_70 (coe v1) (coe v2)
                (coe (\ v4 -> coe du_embed_132 (coe v3 v4)))
         MAlonzo.Code.Once.Lang.Trace.C_halt_122 v1 v2
           -> coe C_halt'8734'_74 (coe v1) (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Lang.Iterative.NodeEq
d_NodeEq_158 a0 a1 a2 a3 a4 a5 a6 = ()
data T_NodeEq_158
  = C_ret'8776''8734'_174 AgdaAny |
    C_call'8776''8734'_186 (AgdaAny -> AgdaAny) |
    C_halt'8776''8734'_192
-- Once.Lang.Iterative.TreeEq∞
d_TreeEq'8734'_202 a0 a1 a2 a3 = ()
data T_TreeEq'8734'_202 = C_constructor_216 T_NodeEq_158
-- Once.Lang.Iterative.TreeEq∞.force≈
d_force'8776'_214 :: T_TreeEq'8734'_202 -> T_NodeEq_158
d_force'8776'_214 v0
  = case coe v0 of
      C_constructor_216 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Iterative.events∞
d_events'8734'_220 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  T_T'8734'_78 ->
  Integer -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_events'8734'_220 ~v0 v1 v2 v3 v4
  = du_events'8734'_220 v1 v2 v3 v4
du_events'8734'_220 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  T_T'8734'_78 ->
  Integer -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_events'8734'_220 v0 v1 v2 v3
  = case coe v3 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
           coe
             (coe
                du_eventsF_224 (coe v0) (coe v1) (coe d_force_84 (coe v2))
                (coe v4))
-- Once.Lang.Iterative.eventsF
d_eventsF_224 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  T_T'8734'F_60 ->
  Integer -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_eventsF_224 ~v0 v1 v2 v3 v4 = du_eventsF_224 v1 v2 v3 v4
du_eventsF_224 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  T_T'8734'F_60 ->
  Integer -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_eventsF_224 v0 v1 v2 v3
  = case coe v2 of
      C_ret'8734'_66 v4
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_call'8734'_70 v4 v5 v6
        -> coe
             du_eventsC_230 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6)
             (coe
                MAlonzo.Code.Once.Lang.Trace.d_callAnswer_330 (coe v0) (coe v1)
                (coe v4) (coe v5))
             (coe v3)
      C_halt'8734'_74 v4 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
             (coe
                MAlonzo.Code.Once.Lang.Trace.d_haltEvent_102 (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Iterative.eventsC
d_eventsC_230 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> T_T'8734'_78) ->
  Maybe AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_eventsC_230 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_eventsC_230 v1 v2 v3 v4 v5 v6 v7
du_eventsC_230 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> T_T'8734'_78) ->
  Maybe AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_eventsC_230 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v2) (coe v3))
             (coe
                du_events'8734'_220 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe
                         MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v2) (coe v3))))
                (coe v4 v7) (coe v6))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
             (coe
                MAlonzo.Code.Once.Lang.Trace.d_haltEvent_102
                (coe MAlonzo.Code.Once.Lang.Trace.d_unlinkedOp_224)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Iterative.ν∞
d_ν'8734'_304 a0 = ()
data T_ν'8734'_304 = C_constructor_312 T_T'8734'_78
-- Once.Lang.Iterative.ν∞.force∞
d_force'8734'_310 :: T_ν'8734'_304 -> T_T'8734'_78
d_force'8734'_310 v0
  = case coe v0 of
      C_constructor_312 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Iterative.ana∞
d_ana'8734'_318 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T'8734'_78) -> AgdaAny -> T_ν'8734'_304
d_ana'8734'_318 v0 ~v1 v2 v3 = du_ana'8734'_318 v0 v2 v3
du_ana'8734'_318 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T'8734'_78) -> AgdaAny -> T_ν'8734'_304
du_ana'8734'_318 v0 v1 v2
  = coe
      C_constructor_312
      (coe du_anaTree'8734'_324 (coe v0) (coe v1) (coe v1 v2))
-- Once.Lang.Iterative.anaTree∞
d_anaTree'8734'_324 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T'8734'_78) -> T_T'8734'_78 -> T_T'8734'_78
d_anaTree'8734'_324 v0 ~v1 v2 v3 = du_anaTree'8734'_324 v0 v2 v3
du_anaTree'8734'_324 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T'8734'_78) -> T_T'8734'_78 -> T_T'8734'_78
du_anaTree'8734'_324 v0 v1 v2
  = coe
      C_constructor_86
      (coe
         du_anaLayer'8734'_330 (coe v0) (coe v1) (coe d_force_84 (coe v2)))
-- Once.Lang.Iterative.anaLayer∞
d_anaLayer'8734'_330 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T'8734'_78) -> T_T'8734'F_60 -> T_T'8734'F_60
d_anaLayer'8734'_330 v0 ~v1 v2 v3 = du_anaLayer'8734'_330 v0 v2 v3
du_anaLayer'8734'_330 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T'8734'_78) -> T_T'8734'F_60 -> T_T'8734'F_60
du_anaLayer'8734'_330 v0 v1 v2
  = case coe v2 of
      C_ret'8734'_66 v3
        -> coe
             C_ret'8734'_66
             (coe du_mapAna'8734'_338 (coe v0) (coe v0) (coe v1) (coe v3))
      C_call'8734'_70 v3 v4 v5
        -> coe
             C_call'8734'_70 (coe v3) (coe v4)
             (coe
                (\ v6 -> coe du_anaTree'8734'_324 (coe v0) (coe v1) (coe v5 v6)))
      C_halt'8734'_74 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Iterative.mapAna∞
d_mapAna'8734'_338 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T'8734'_78) -> AgdaAny -> AgdaAny
d_mapAna'8734'_338 v0 v1 ~v2 v3 v4
  = du_mapAna'8734'_338 v0 v1 v3 v4
du_mapAna'8734'_338 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T'8734'_78) -> AgdaAny -> AgdaAny
du_mapAna'8734'_338 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe du_ana'8734'_318 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'8734'_338 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'8734'_338 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'8734'_338 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'8734'_338 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Iterative._.⟦_⟧F
d_'10214'_'10215'F_426 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_426 = erased
-- Once.Lang.Iterative.fmap∞
d_fmap'8734'_432 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_T'8734'_78 -> T_T'8734'_78
d_fmap'8734'_432 ~v0 ~v1 v2 v3 = du_fmap'8734'_432 v2 v3
du_fmap'8734'_432 ::
  (AgdaAny -> AgdaAny) -> T_T'8734'_78 -> T_T'8734'_78
du_fmap'8734'_432 v0 v1
  = coe
      du__'62''62''61''8734'__98 (coe v1)
      (coe (\ v2 -> coe du_return'8734'_90 (coe v0 v2)))
-- Once.Lang.Iterative.seqF∞
d_seqF'8734'_444 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> AgdaAny -> T_T'8734'_78
d_seqF'8734'_444 v0 ~v1 v2 = du_seqF'8734'_444 v0 v2
du_seqF'8734'_444 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> AgdaAny -> T_T'8734'_78
du_seqF'8734'_444 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v2
        -> coe du_return'8734'_90 (coe v1)
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    du_fmap'8734'_432 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe du_seqF'8734'_444 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    du_fmap'8734'_432 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe du_seqF'8734'_444 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du__'62''62''61''8734'__98
                    (coe du_seqF'8734'_444 (coe v2) (coe v4))
                    (coe
                       (\ v6 ->
                          coe
                            du__'62''62''61''8734'__98
                            (coe du_seqF'8734'_444 (coe v3) (coe v5))
                            (coe
                               (\ v7 ->
                                  coe
                                    du_return'8734'_90
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
