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

module MAlonzo.Code.Once.Semantics.Machine where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Res
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Type

-- Once.Semantics.Machine._.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Semantics.Machine._.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Semantics.Machine._.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor_246 v0 v2
-- Once.Semantics.Machine._.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor'8315''185'_288
      v0 v2
-- Once.Semantics.Machine._.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Semantics.Machine._.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Semantics.Machine._.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_578
-- Once.Semantics.Machine._.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_584
-- Once.Semantics.Machine._.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Internal.Value.du_erase'7501'_104
-- Once.Semantics.Machine._.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoIn_598
-- Once.Semantics.Machine._.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoOut_588
-- Once.Semantics.Machine._.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_μS_82
d_sem'45'In_30
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'In_518
-- Once.Semantics.Machine._.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'Out_526
-- Once.Semantics.Machine._.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Semantics.Machine._.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Semantics.Machine._.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Semantics.Machine._.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Semantics.Machine._.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Semantics.Machine._.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Semantics.Machine._.⟦_⟧
d_'10214'_'10215'_46 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Semantics.Machine._.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Semantics.Machine._.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Semantics.Machine._.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Semantics.Machine._.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Semantics.Machine._.base-coh
d_base'45'coh_58 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'coh_58 = erased
-- Once.Semantics.Machine._.coh
d_coh_60 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coh_60 = erased
-- Once.Semantics.Machine._.tF-coh
d_tF'45'coh_62 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tF'45'coh_62 = erased
-- Once.Semantics.Machine._.⟦_⟧Fᴵ
d_'10214'_'10215'F'7477'_64 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> () -> ()
d_'10214'_'10215'F'7477'_64 = erased
-- Once.Semantics.Machine._.⟦_⟧ᴵ
d_'10214'_'10215''7477'_66 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7477'_66 = erased
-- Once.Semantics.Machine.LitPayload
d_LitPayload_70 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 -> ()
d_LitPayload_70 = erased
