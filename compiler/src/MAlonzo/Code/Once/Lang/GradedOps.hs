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

module MAlonzo.Code.Once.Lang.GradedOps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.FunctorMeaning
import qualified MAlonzo.Code.Once.Lang.Graded
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Name
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Stream
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Lang.GradedOps.Val.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Lang.GradedOps.Val.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Lang.GradedOps.Val.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_246 v0 v2
-- Once.Lang.GradedOps.Val.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_288 v0
      v2
-- Once.Lang.GradedOps.Val.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Lang.GradedOps.Val.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Lang.GradedOps.Val.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.Lang.GradedOps.Val.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
-- Once.Lang.GradedOps.Val.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104
-- Once.Lang.GradedOps.Val.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_598
-- Once.Lang.GradedOps.Val.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_588
-- Once.Lang.GradedOps.Val.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_30 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518
-- Once.Lang.GradedOps.Val.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_526
-- Once.Lang.GradedOps.Val.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Lang.GradedOps.Val.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Lang.GradedOps.Val.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Lang.GradedOps.Val.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Lang.GradedOps.Val.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Lang.GradedOps.Val.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Lang.GradedOps.Val.⟦_⟧
d_'10214'_'10215'_46 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Lang.GradedOps.Val.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Lang.GradedOps.Val.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Lang.GradedOps.Val.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Lang.GradedOps.Val.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Lang.GradedOps._.coerce-ν-in
d_coerce'45'ν'45'in_58 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_58
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.Lang.GradedOps._.coerce-ν-out
d_coerce'45'ν'45'out_60 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_60
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
-- Once.Lang.GradedOps._.sem-In
d_sem'45'In_62 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_62 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518
-- Once.Lang.GradedOps._.sem-cata
d_sem'45'cata_64 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_64 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Lang.GradedOps._.sem-fmap
d_sem'45'fmap_66 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_66 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Lang.GradedOps._.⟦_⟧F
d_'10214'_'10215'F_68 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_68 = erased
-- Once.Lang.GradedOps.fmapM
d_fmapM_76 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmapM_76 v0 ~v1 ~v2 v3 v4 = du_fmapM_76 v0 v3 v4
du_fmapM_76 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmapM_76 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34 -> coe v1 v2
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe MAlonzo.Code.Once.Lang.Trace.du_fmapT_170 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_432 (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.injB
d_injB_92 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_injB_92 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Void_12 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_injB_92 (coe v7) (coe v5) (coe v9))
                           (coe d_injB_92 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_injB_92 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_injB_92 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.prjB
d_prjB_124 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_prjB_124 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Void_12 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_prjB_124 (coe v7) (coe v5) (coe v9))
                           (coe d_prjB_124 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_prjB_124 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_prjB_124 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.cfᵛ
d_cf'7515'_158 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_cf'7515'_158 v0 ~v1 v2 v3 = du_cf'7515'_158 v0 v2 v3
du_cf'7515'_158 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_cf'7515'_158 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'K_52 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_K_12 v5
               -> coe d_prjB_124 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Id_54 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_cf'7515'_158 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_cf'7515'_158 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_cf'7515'_158 (coe v7) (coe v5) (coe v9))
                           (coe du_cf'7515'_158 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.cf⁻¹ᵛ
d_cf'8315''185''7515'_200 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_cf'8315''185''7515'_200 v0 ~v1 v2 v3
  = du_cf'8315''185''7515'_200 v0 v2 v3
du_cf'8315''185''7515'_200 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_cf'8315''185''7515'_200 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'K_52 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_K_12 v5
               -> coe d_injB_92 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Id_54 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_cf'8315''185''7515'_200 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_cf'8315''185''7515'_200 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_cf'8315''185''7515'_200 (coe v7) (coe v5) (coe v9))
                           (coe du_cf'8315''185''7515'_200 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.seqM
d_seqM_244 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_seqM_244 ~v0 v1 v2 ~v3 v4 = du_seqM_244 v1 v2 v4
du_seqM_244 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> AgdaAny -> AgdaAny
du_seqM_244 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v2
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.du_seqF'8734'_444 (coe v1)
             (coe v2)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
        -> coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.in-valueᵛ
d_in'45'value'7515'_260 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_in'45'value'7515'_260 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518 (coe v0)
      (coe du_cf'7515'_158 (coe v0) (coe v1) (coe v2))
-- Once.Lang.GradedOps.cata-semᵛ
d_cata'45'sem'7515'_274 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_cata'45'sem'7515'_274 v0 v1 v2 ~v3 v4 v5
  = du_cata'45'sem'7515'_274 v0 v1 v2 v4 v5
du_cata'45'sem'7515'_274 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
du_cata'45'sem'7515'_274 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 (coe v2) (coe v3)
      (coe
         (\ v5 ->
            coe
              MAlonzo.Code.Once.Lang.Graded.du_bindM_80 (coe v0)
              (coe du_seqM_244 (coe v1) (coe v2) (coe v5))
              (coe
                 (\ v6 ->
                    coe
                      v4 (coe du_cf'8315''185''7515'_200 (coe v2) (coe v3) (coe v6))))))
-- Once.Lang.GradedOps.mapLayerᵛ
d_mapLayer'7515'_300 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_mapLayer'7515'_300 v0 v1 v2 ~v3 ~v4 v5 v6 v7
  = du_mapLayer'7515'_300 v0 v1 v2 v5 v6 v7
du_mapLayer'7515'_300 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_mapLayer'7515'_300 v0 v1 v2 v3 v4 v5
  = coe
      du_fmapM_76 (coe v0)
      (coe du_cf'8315''185''7515'_200 (coe v2) (coe v3))
      (coe
         du_seqM_244 (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 (coe v2) (coe v4)
            (coe du_cf'7515'_158 (coe v2) (coe v3) (coe v5))))
-- Once.Lang.GradedOps.anaᵖ
d_ana'7510'_322 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_198
d_ana'7510'_322 v0 ~v1 v2 v3 = du_ana'7510'_322 v0 v2 v3
du_ana'7510'_322 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_198
du_ana'7510'_322 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Graded.C_constructor_206
      (coe du_mapAna'7510'_330 (coe v0) (coe v0) (coe v1) (coe v1 v2))
-- Once.Lang.GradedOps.mapAnaᵖ
d_mapAna'7510'_330 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_mapAna'7510'_330 v0 v1 ~v2 v3 v4
  = du_mapAna'7510'_330 v0 v1 v3 v4
du_mapAna'7510'_330 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_mapAna'7510'_330 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe du_ana'7510'_322 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'7510'_330 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'7510'_330 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'7510'_330 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'7510'_330 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.embνᵃ
d_embν'7491'_386 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_198 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14
d_embν'7491'_386 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Stream.C_constructor_22
      (coe
         MAlonzo.Code.Once.Lang.Trace.C_ret_114
         (coe
            d_mapEmbν'7491'_392 (coe v0) (coe v0)
            (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_204 (coe v1))))
-- Once.Lang.GradedOps.mapEmbνᵃ
d_mapEmbν'7491'_392 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_mapEmbν'7491'_392 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v2
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe d_embν'7491'_386 (coe v0) (coe v2)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_mapEmbν'7491'_392 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_mapEmbν'7491'_392 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_mapEmbν'7491'_392 (coe v0) (coe v3) (coe v5))
                    (coe d_mapEmbν'7491'_392 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.ana-semᵛ
d_ana'45'sem'7515'_440 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_ana'45'sem'7515'_440 v0 ~v1 v2 v3 v4 v5
  = du_ana'45'sem'7515'_440 v0 v2 v3 v4 v5
du_ana'45'sem'7515'_440 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_ana'45'sem'7515'_440 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
        -> coe
             du_ana'7510'_322
             (coe
                MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased
                     (coe du_cf'7515'_158 (coe v0) (coe v2) (coe v3 v5))))
             (coe v4)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
        -> coe
             MAlonzo.Code.Once.Lang.Stream.du_ana'7496'_70
             (coe
                MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased
                             (coe du_cf'7515'_158 (coe v0) (coe v2) (coe v6))))
                     (coe v3 v5)))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.out-semᵛ
d_out'45'sem'7515'_472 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_out'45'sem'7515'_472 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
        -> coe
             du_cf'8315''185''7515'_200 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584 v1 v2 erased
                (MAlonzo.Code.Once.Lang.Graded.d_force'7510'_204 (coe v3)))
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
             (coe
                (\ v4 ->
                   coe
                     du_cf'8315''185''7515'_200 (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584 v1 v2 erased
                        v4)))
             (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.⟦_⟧<:ᵛ
d_'10214'_'10215''60''58''7515'_492 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  AgdaAny -> AgdaAny
d_'10214'_'10215''60''58''7515'_492 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_30
        -> coe (\ v4 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_32
        -> coe (\ v3 -> v3)
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_34 -> coe (\ v3 -> v3)
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_36
        -> coe (\ v3 -> v3)
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v10 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v16 v17
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                    -> coe
                                         (\ v21 v22 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Graded.du_subM_100 (coe v12)
                                              (coe
                                                 du_fmapM_76 (coe v17)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_492 (coe v15)
                                                    (coe v20) (coe v11))
                                                 (coe v21 v22)))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                    -> coe
                                         (\ v21 v22 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Graded.du_subM_100 (coe v12)
                                              (coe
                                                 du_fmapM_76 (coe v17)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_492 (coe v15)
                                                    (coe v20) (coe v11))
                                                 (coe
                                                    v21
                                                    (coe
                                                       d_'10214'_'10215''60''58''7515'_492 v18 v13
                                                       v10 v22))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                                    -> coe
                                         (\ v21 v22 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Graded.du_subM_100 (coe v12)
                                              (coe
                                                 du_fmapM_76 (coe v17)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_492 (coe v15)
                                                    (coe v20) (coe v11))
                                                 (coe
                                                    v21
                                                    (coe
                                                       d_'10214'_'10215''60''58''7515'_492 v18 v13
                                                       v10 v22))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
                      -> coe
                           (\ v13 ->
                              case coe v13 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe d_'10214'_'10215''60''58''7515'_492 v9 v11 v7 v14)
                                       (coe d_'10214'_'10215''60''58''7515'_492 v10 v12 v8 v15)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_72 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
                      -> coe
                           (\ v13 ->
                              case coe v13 of
                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                  -> coe
                                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                       (coe d_'10214'_'10215''60''58''7515'_492 v9 v11 v7 v14)
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                  -> coe
                                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                       (coe d_'10214'_'10215''60''58''7515'_492 v10 v12 v8 v14)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_76 -> coe (\ v4 -> v4)
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_84 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v9 v10
                      -> case coe v8 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42 -> coe (\ v11 -> v11)
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
                                    -> coe
                                         (\ v11 ->
                                            d_embν'7491'_386
                                              (coe
                                                 MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56
                                                 (coe v7))
                                              (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
                             -> coe seq (coe v10) (coe (\ v11 -> v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'rigid_90
        -> coe (\ v5 -> v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.opCallᵀ
d_opCall'7488'_570 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_opCall'7488'_570 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Once.Lang.Trace.C_halt_122
                       (coe
                          MAlonzo.Code.Once.Lang.Trace.C_haltOp_90 (coe v2) (coe v0)
                          (coe v3))
                       (coe v6))
             else coe
                    seq (coe v8)
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Trace.C_call_118
                                        (coe
                                           MAlonzo.Code.Once.Lang.Trace.C_callOp_74 (coe v2)
                                           (coe v0) (coe v3)
                                           (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                        (coe v6)
                                        (coe
                                           (\ v11 ->
                                              coe
                                                MAlonzo.Code.Once.Lang.Trace.C_ret_114
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                              else coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Trace.C_call_118
                                        (coe
                                           MAlonzo.Code.Once.Lang.Trace.C_callOp_74 (coe v2)
                                           (coe v0) (coe v3) (coe v1))
                                        (coe v6) (coe MAlonzo.Code.Once.Lang.Trace.C_ret_114))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.sigOpRefᵛ
d_sigOpRef'7515'_606 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_sigOpRef'7515'_606 v0 ~v1 v2 v3 v4 v5 ~v6
  = du_sigOpRef'7515'_606 v0 v2 v3 v4 v5
du_sigOpRef'7515'_606 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 -> AgdaAny
du_sigOpRef'7515'_606 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v6
        -> coe
             d_injB_92 (coe v0) (coe v6)
             (coe
                MAlonzo.Code.Once.Lang.Contract.du_valueOf_290 v1 v2
                (coe
                   MAlonzo.Code.Once.Lang.Contract.C_key_70
                   (coe MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v3))
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                                    -> coe
                                         (\ v15 ->
                                            d_injB_92
                                              (coe v12) (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Contract.du_valueOf_290 v1
                                                 v2
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Contract.C_key_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Name.d_showCanonical_6
                                                       (coe v3))
                                                    (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                    (coe v12))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                              (coe d_injB_92 (coe v12) (coe v9))
                                              (coe
                                                 d_opCall'7488'_570
                                                 (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                 (coe v12) (coe v3)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                    (coe v12))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                    (coe v12))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Iterative.du_embed_132
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                                 (coe d_injB_92 (coe v12) (coe v9))
                                                 (coe
                                                    d_opCall'7488'_570
                                                    (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                    (coe v12) (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                       (coe v12))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                       (coe v12))
                                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                                    -> coe
                                         (\ v15 ->
                                            d_injB_92
                                              (coe v12) (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Contract.du_valueOf_290 v1
                                                 v2
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Contract.C_key_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Name.d_showCanonical_6
                                                       (coe v3))
                                                    (coe v10) (coe v12))
                                                 (d_prjB_124 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                              (coe d_injB_92 (coe v12) (coe v9))
                                              (coe
                                                 d_opCall'7488'_570 (coe v10) (coe v12) (coe v3)
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                    (coe v12))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                    (coe v12))
                                                 (coe d_prjB_124 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Iterative.du_embed_132
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                                 (coe d_injB_92 (coe v12) (coe v9))
                                                 (coe
                                                    d_opCall'7488'_570 (coe v10) (coe v12) (coe v3)
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                       (coe v12))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                       (coe v12))
                                                    (coe d_prjB_124 (coe v10) (coe v8) (coe v15)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                                    -> coe
                                         (\ v15 ->
                                            d_injB_92
                                              (coe v12) (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Contract.du_valueOf_290 v1
                                                 v2
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Contract.C_key_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Name.d_showCanonical_6
                                                       (coe v3))
                                                    (coe v10) (coe v12))
                                                 (d_prjB_124 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                              (coe d_injB_92 (coe v12) (coe v9))
                                              (coe
                                                 d_opCall'7488'_570 (coe v10) (coe v12) (coe v3)
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                    (coe v12))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                    (coe v12))
                                                 (coe d_prjB_124 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Iterative.du_embed_132
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                                 (coe d_injB_92 (coe v12) (coe v9))
                                                 (coe
                                                    d_opCall'7488'_570 (coe v10) (coe v12) (coe v3)
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                       (coe v12))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                       (coe v12))
                                                    (coe d_prjB_124 (coe v10) (coe v8) (coe v15)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
