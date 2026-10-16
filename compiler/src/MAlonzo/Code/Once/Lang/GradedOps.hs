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
import qualified MAlonzo.Code.Once.Lang.Guarded
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
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_440
-- Once.Lang.GradedOps.Val.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_408
-- Once.Lang.GradedOps.Val.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_282 v0 v2
-- Once.Lang.GradedOps.Val.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_324 v0
      v2
-- Once.Lang.GradedOps.Val.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_472 v0 v2
-- Once.Lang.GradedOps.Val.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_514 v0 v1 v3
-- Once.Lang.GradedOps.Val.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_614
-- Once.Lang.GradedOps.Val.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_620
-- Once.Lang.GradedOps.Val.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_116
-- Once.Lang.GradedOps.Val.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_634
-- Once.Lang.GradedOps.Val.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_624
-- Once.Lang.GradedOps.Val.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_30 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_554
-- Once.Lang.GradedOps.Val.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_562
-- Once.Lang.GradedOps.Val.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_644 v0 v2 v3
-- Once.Lang.GradedOps.Val.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_574 v0 v1 v3
-- Once.Lang.GradedOps.Val.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_368 v0 v3 v4
-- Once.Lang.GradedOps.Val.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_590 v0 v1 v3 v4
-- Once.Lang.GradedOps.Val.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_650 v0 v2 v3
-- Once.Lang.GradedOps.Val.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_658 v0 v1 v3 v4
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
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_614
-- Once.Lang.GradedOps._.coerce-ν-out
d_coerce'45'ν'45'out_60 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_60
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_620
-- Once.Lang.GradedOps._.sem-In
d_sem'45'In_62 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_62 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_554
-- Once.Lang.GradedOps._.sem-cata
d_sem'45'cata_64 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_64 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_574 v0 v1 v3
-- Once.Lang.GradedOps._.sem-fmap
d_sem'45'fmap_66 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_66 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_368 v0 v3 v4
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
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> coe
             MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_432 (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.injB
d_injB_96 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_injB_96 v0 v1 v2
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
                           (coe d_injB_96 (coe v7) (coe v5) (coe v9))
                           (coe d_injB_96 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_injB_96 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_injB_96 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.prjB
d_prjB_128 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_prjB_128 v0 v1 v2
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
                           (coe d_prjB_128 (coe v7) (coe v5) (coe v9))
                           (coe d_prjB_128 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_prjB_128 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_prjB_128 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.cfᵛ
d_cf'7515'_162 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_cf'7515'_162 v0 ~v1 v2 v3 = du_cf'7515'_162 v0 v2 v3
du_cf'7515'_162 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_cf'7515'_162 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'K_52 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_K_12 v5
               -> coe d_prjB_128 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Id_54 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_cf'7515'_162 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_cf'7515'_162 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_cf'7515'_162 (coe v7) (coe v5) (coe v9))
                           (coe du_cf'7515'_162 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.cf⁻¹ᵛ
d_cf'8315''185''7515'_204 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_cf'8315''185''7515'_204 v0 ~v1 v2 v3
  = du_cf'8315''185''7515'_204 v0 v2 v3
du_cf'8315''185''7515'_204 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_cf'8315''185''7515'_204 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'K_52 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_K_12 v5
               -> coe d_injB_96 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Id_54 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_cf'8315''185''7515'_204 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_cf'8315''185''7515'_204 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_cf'8315''185''7515'_204 (coe v7) (coe v5) (coe v9))
                           (coe du_cf'8315''185''7515'_204 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.seqM
d_seqM_248 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_seqM_248 ~v0 v1 v2 ~v3 v4 = du_seqM_248 v1 v2 v4
du_seqM_248 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> AgdaAny -> AgdaAny
du_seqM_248 v0 v1 v2
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
d_in'45'value'7515'_264 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_in'45'value'7515'_264 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_sem'45'In_554 (coe v0)
      (coe du_cf'7515'_162 (coe v0) (coe v1) (coe v2))
-- Once.Lang.GradedOps.cata-semᵛ
d_cata'45'sem'7515'_278 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_cata'45'sem'7515'_278 v0 v1 v2 ~v3 v4 v5
  = du_cata'45'sem'7515'_278 v0 v1 v2 v4 v5
du_cata'45'sem'7515'_278 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
du_cata'45'sem'7515'_278 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_574 (coe v2) (coe v3)
      (coe
         (\ v5 ->
            coe
              MAlonzo.Code.Once.Lang.Graded.du_bindM_82 (coe v0)
              (coe du_seqM_248 (coe v1) (coe v2) (coe v5))
              (coe
                 (\ v6 ->
                    coe
                      v4 (coe du_cf'8315''185''7515'_204 (coe v2) (coe v3) (coe v6))))))
-- Once.Lang.GradedOps.mapLayerᵛ
d_mapLayer'7515'_304 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_mapLayer'7515'_304 v0 v1 v2 ~v3 ~v4 v5 v6 v7
  = du_mapLayer'7515'_304 v0 v1 v2 v5 v6 v7
du_mapLayer'7515'_304 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_mapLayer'7515'_304 v0 v1 v2 v3 v4 v5
  = coe
      du_fmapM_76 (coe v0)
      (coe du_cf'8315''185''7515'_204 (coe v2) (coe v3))
      (coe
         du_seqM_248 (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_368 (coe v2) (coe v4)
            (coe du_cf'7515'_162 (coe v2) (coe v3) (coe v5))))
-- Once.Lang.GradedOps.anaᵖ
d_ana'7510'_326 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_244
d_ana'7510'_326 v0 ~v1 v2 v3 = du_ana'7510'_326 v0 v2 v3
du_ana'7510'_326 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_244
du_ana'7510'_326 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Graded.C_constructor_252
      (coe du_mapAna'7510'_334 (coe v0) (coe v0) (coe v1) (coe v1 v2))
-- Once.Lang.GradedOps.mapAnaᵖ
d_mapAna'7510'_334 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_mapAna'7510'_334 v0 v1 ~v2 v3 v4
  = du_mapAna'7510'_334 v0 v1 v3 v4
du_mapAna'7510'_334 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_mapAna'7510'_334 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe du_ana'7510'_326 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'7510'_334 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'7510'_334 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'7510'_334 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'7510'_334 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.embν
d_embν_390 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_244 ->
  MAlonzo.Code.Once.Lang.Iterative.T_ν'8734'_304
d_embν_390 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_312
      (coe
         MAlonzo.Code.Once.Lang.Iterative.C_constructor_86
         (coe
            MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66
            (coe
               d_mapEmbν_396 (coe v0) (coe v0)
               (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_250 (coe v1)))))
-- Once.Lang.GradedOps.mapEmbν
d_mapEmbν_396 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_mapEmbν_396 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v2
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe d_embν_390 (coe v0) (coe v2)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_mapEmbν_396 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_mapEmbν_396 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_mapEmbν_396 (coe v0) (coe v3) (coe v5))
                    (coe d_mapEmbν_396 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.embνᵃ
d_embν'7491'_440 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_244 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14
d_embν'7491'_440 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Stream.C_constructor_22
      (coe
         MAlonzo.Code.Once.Lang.Trace.C_ret_114
         (coe
            d_mapEmbν'7491'_446 (coe v0) (coe v0)
            (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_250 (coe v1))))
-- Once.Lang.GradedOps.mapEmbνᵃ
d_mapEmbν'7491'_446 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_mapEmbν'7491'_446 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v2
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe d_embν'7491'_440 (coe v0) (coe v2)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_mapEmbν'7491'_446 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_mapEmbν'7491'_446 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_mapEmbν'7491'_446 (coe v0) (coe v3) (coe v5))
                    (coe d_mapEmbν'7491'_446 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.embν∞ᵈ
d_embν'8734''7496'_490 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  MAlonzo.Code.Once.Lang.Iterative.T_ν'8734'_304
d_embν'8734''7496'_490 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_312
      (coe
         d_embLay'8734'_494 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v1)))
-- Once.Lang.GradedOps.embLay∞
d_embLay'8734'_494 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
d_embLay'8734'_494 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_86
      (case coe v1 of
         MAlonzo.Code.Once.Lang.Trace.C_ret_114 v2
           -> coe
                MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66
                (coe d_mapEmbν'8734''7496'_500 (coe v0) (coe v0) (coe v2))
         MAlonzo.Code.Once.Lang.Trace.C_call_118 v2 v3 v4
           -> coe
                MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 (coe v2) (coe v3)
                (coe (\ v5 -> d_embLay'8734'_494 (coe v0) (coe v4 v5)))
         MAlonzo.Code.Once.Lang.Trace.C_halt_122 v2 v3
           -> coe
                MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 (coe v2) (coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Lang.GradedOps.mapEmbν∞ᵈ
d_mapEmbν'8734''7496'_500 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_mapEmbν'8734''7496'_500 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v2
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe d_embν'8734''7496'_490 (coe v0) (coe v2)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_mapEmbν'8734''7496'_500 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_mapEmbν'8734''7496'_500 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_mapEmbν'8734''7496'_500 (coe v0) (coe v3) (coe v5))
                    (coe d_mapEmbν'8734''7496'_500 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.ana-semᵛ
d_ana'45'sem'7515'_568 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_ana'45'sem'7515'_568 v0 ~v1 v2 v3 v4 v5
  = du_ana'45'sem'7515'_568 v0 v2 v3 v4 v5
du_ana'45'sem'7515'_568 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_ana'45'sem'7515'_568 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe
             du_ana'7510'_326
             (coe
                MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_614 v0 erased
                     (coe du_cf'7515'_162 (coe v0) (coe v2) (coe v3 v5))))
             (coe v4)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
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
                             MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_614 v0 erased
                             (coe du_cf'7515'_162 (coe v0) (coe v2) (coe v6))))
                     (coe v3 v5)))
             (coe v4)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> coe
             MAlonzo.Code.Once.Lang.Guarded.du_ana'8314'_178
             (coe
                MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_614 v0 erased
                             (coe du_cf'7515'_162 (coe v0) (coe v2) (coe v6))))
                     (coe v3 v5)))
             (coe v4)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.du_ana'8734'_318
             (coe
                MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_432
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_614 v0 erased
                             (coe du_cf'7515'_162 (coe v0) (coe v2) (coe v6))))
                     (coe v3 v5)))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.out-semᵛ
d_out'45'sem'7515'_628 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_out'45'sem'7515'_628 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe
             du_cf'8315''185''7515'_204 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_620 v1 v2 erased
                (MAlonzo.Code.Once.Lang.Graded.d_force'7510'_250 (coe v3)))
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
             (coe
                (\ v4 ->
                   coe
                     du_cf'8315''185''7515'_204 (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_620 v1 v2 erased
                        v4)))
             (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> coe
             MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
             (coe
                (\ v4 ->
                   coe
                     du_cf'8315''185''7515'_204 (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_620 v1 v2 erased
                        v4)))
             (coe MAlonzo.Code.Once.Lang.Guarded.d_force'8314'_170 (coe v3))
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_432
             (coe
                (\ v4 ->
                   coe
                     du_cf'8315''185''7515'_204 (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_620 v1 v2 erased
                        v4)))
             (coe MAlonzo.Code.Once.Lang.Iterative.d_force'8734'_310 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.embν⁺
d_embν'8314'_662 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Guarded.T_ν'8314'_164 ->
  MAlonzo.Code.Once.Lang.Iterative.T_ν'8734'_304
d_embν'8314'_662 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_312
      (coe
         d_embRoot'8314'_666 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Guarded.d_force'8314'_170 (coe v1)))
-- Once.Lang.GradedOps.embRoot⁺
d_embRoot'8314'_666 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
d_embRoot'8314'_666 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_86
      (case coe v1 of
         MAlonzo.Code.Once.Lang.Guarded.C_call'8314'_64 v2 v3 v4
           -> coe
                MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 (coe v2) (coe v3)
                (coe (\ v5 -> d_embTree'8314'_670 (coe v0) (coe v4 v5)))
         MAlonzo.Code.Once.Lang.Guarded.C_halt'8314'_68 v2 v3
           -> coe
                MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 (coe v2) (coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Lang.GradedOps.embTree⁺
d_embTree'8314'_670 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
d_embTree'8314'_670 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_86
      (coe
         d_embLayer'8314'_674 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v1)))
-- Once.Lang.GradedOps.embLayer⁺
d_embLayer'8314'_674 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
d_embLayer'8314'_674 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v2
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66
             (coe d_mapEmbν'8314'_680 (coe v0) (coe v0) (coe v2))
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 (coe v2) (coe v3)
             (coe (\ v5 -> d_embTree'8314'_670 (coe v0) (coe v4 v5)))
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.mapEmbν⁺
d_mapEmbν'8314'_680 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_mapEmbν'8314'_680 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v2
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe d_embν'8314'_662 (coe v0) (coe v2)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_mapEmbν'8314'_680 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_mapEmbν'8314'_680 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_mapEmbν'8314'_680 (coe v0) (coe v3) (coe v5))
                    (coe d_mapEmbν'8314'_680 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.⟦_⟧<:ᵛ
d_'10214'_'10215''60''58''7515'_766 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  AgdaAny -> AgdaAny
d_'10214'_'10215''60''58''7515'_766 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_36 -> coe v3
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_38 -> coe v3
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_40 -> coe v3
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56 v11 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v17 v18
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Graded.du_subM_108 (coe v13)
                                              (coe
                                                 du_fmapM_76 (coe v18)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_766 (coe v16)
                                                    (coe v21) (coe v12))
                                                 (coe v3 v22)))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Graded.du_subM_108 (coe v13)
                                              (coe
                                                 du_fmapM_76 (coe v18)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_766 (coe v16)
                                                    (coe v21) (coe v12))
                                                 (coe
                                                    v3
                                                    (d_'10214'_'10215''60''58''7515'_766
                                                       (coe v19) (coe v14) (coe v11) (coe v22)))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Graded.du_subM_108 (coe v13)
                                              (coe
                                                 du_fmapM_76 (coe v18)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_766 (coe v16)
                                                    (coe v21) (coe v12))
                                                 (coe
                                                    v3
                                                    (d_'10214'_'10215''60''58''7515'_766
                                                       (coe v19) (coe v14) (coe v11) (coe v22)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_66 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_766 (coe v10) (coe v12)
                                     (coe v8) (coe v14))
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_766 (coe v11) (coe v13)
                                     (coe v9) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'sum_76 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_766 (coe v10) (coe v12)
                                     (coe v8) (coe v14))
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_766 (coe v11) (coe v13)
                                     (coe v9) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'μ_80 -> coe v3
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'ν_88 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v8 v9
               -> case coe v7 of
                    MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v3
                    MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v3
                    MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
                      -> coe
                           d_embν_390
                           (coe
                              MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v8))
                           (coe v3)
                    MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16 -> coe v3
                    MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
                      -> coe
                           d_embν'7491'_440
                           (coe
                              MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v8))
                           (coe v3)
                    MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
                      -> coe
                           d_embν'8734''7496'_490
                           (coe
                              MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v8))
                           (coe v3)
                    MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22 -> coe v3
                    MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
                      -> coe
                           d_embν'8314'_662
                           (coe
                              MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v8))
                           (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'rigid_94 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.opCall⁺
d_opCall'8314'_854 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58
d_opCall'8314'_854 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Once.Lang.Guarded.C_halt'8314'_68
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
                                        MAlonzo.Code.Once.Lang.Guarded.C_call'8314'_64
                                        (coe
                                           MAlonzo.Code.Once.Lang.Trace.C_callOp_74 (coe v2)
                                           (coe v0) (coe v3)
                                           (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                        (coe v6)
                                        (coe
                                           (\ v11 ->
                                              coe
                                                MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                              else coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Guarded.C_call'8314'_64
                                        (coe
                                           MAlonzo.Code.Once.Lang.Trace.C_callOp_74 (coe v2)
                                           (coe v0) (coe v3) (coe v1))
                                        (coe v6)
                                        (coe MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.opCallᵀ
d_opCall'7488'_888 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_opCall'7488'_888 v0 v1 v2 v3 v4 v5 v6
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
d_sigOpRef'7515'_924 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_sigOpRef'7515'_924 v0 ~v1 v2 v3 v4 v5 ~v6
  = du_sigOpRef'7515'_924 v0 v2 v3 v4 v5
du_sigOpRef'7515'_924 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 -> AgdaAny
du_sigOpRef'7515'_924 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v6
        -> coe
             d_injB_96 (coe v0) (coe v6)
             (coe
                MAlonzo.Code.Once.Lang.Contract.du_valueOf_308 v1 v2
                (coe
                   MAlonzo.Code.Once.Lang.Contract.C_key_70
                   (coe MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v3))
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                                    -> coe
                                         (\ v15 ->
                                            d_injB_96
                                              (coe v12) (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Contract.du_valueOf_308 v1
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
                                              (coe d_injB_96 (coe v12) (coe v9))
                                              (coe
                                                 d_opCall'7488'_888
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
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                                              (coe d_injB_96 (coe v12) (coe v9))
                                              (coe
                                                 d_opCall'8314'_854
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
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                                                 (coe d_injB_96 (coe v12) (coe v9))
                                                 (coe
                                                    d_opCall'8314'_854
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
                                            d_injB_96
                                              (coe v12) (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Contract.du_valueOf_308 v1
                                                 v2
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Contract.C_key_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Name.d_showCanonical_6
                                                       (coe v3))
                                                    (coe v10) (coe v12))
                                                 (d_prjB_128 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                              (coe d_injB_96 (coe v12) (coe v9))
                                              (coe
                                                 d_opCall'7488'_888 (coe v10) (coe v12) (coe v3)
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                    (coe v12))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                    (coe v12))
                                                 (coe d_prjB_128 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                                              (coe d_injB_96 (coe v12) (coe v9))
                                              (coe
                                                 d_opCall'8314'_854 (coe v10) (coe v12) (coe v3)
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                    (coe v12))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                    (coe v12))
                                                 (coe d_prjB_128 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                                                 (coe d_injB_96 (coe v12) (coe v9))
                                                 (coe
                                                    d_opCall'8314'_854 (coe v10) (coe v12) (coe v3)
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                       (coe v12))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                       (coe v12))
                                                    (coe d_prjB_128 (coe v10) (coe v8) (coe v15)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                                    -> coe
                                         (\ v15 ->
                                            d_injB_96
                                              (coe v12) (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Contract.du_valueOf_308 v1
                                                 v2
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Contract.C_key_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Name.d_showCanonical_6
                                                       (coe v3))
                                                    (coe v10) (coe v12))
                                                 (d_prjB_128 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                              (coe d_injB_96 (coe v12) (coe v9))
                                              (coe
                                                 d_opCall'7488'_888 (coe v10) (coe v12) (coe v3)
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                    (coe v12))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                    (coe v12))
                                                 (coe d_prjB_128 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                                              (coe d_injB_96 (coe v12) (coe v9))
                                              (coe
                                                 d_opCall'8314'_854 (coe v10) (coe v12) (coe v3)
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                    (coe v12))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                    (coe v12))
                                                 (coe d_prjB_128 (coe v10) (coe v8) (coe v15))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
                                    -> coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                                                 (coe d_injB_96 (coe v12) (coe v9))
                                                 (coe
                                                    d_opCall'8314'_854 (coe v10) (coe v12) (coe v3)
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84
                                                       (coe v12))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88
                                                       (coe v12))
                                                    (coe d_prjB_128 (coe v10) (coe v8) (coe v15)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.GradedOps.sigOpGuardᵛ
d_sigOpGuard'7515'_1180 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 -> AgdaAny
d_sigOpGuard'7515'_1180 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                  (coe d_injB_96 (coe v1) (coe v4))
                  (coe
                     d_opCall'8314'_854 (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                     (coe v1) (coe v2)
                     (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                     (coe MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84 (coe v1))
                     (coe MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88 (coe v1))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                  (coe d_injB_96 (coe v1) (coe v4))
                  (coe
                     d_opCall'8314'_854 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84 (coe v1))
                     (coe MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88 (coe v1))
                     (coe d_prjB_128 (coe v0) (coe v3) (coe v6))))
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Lang.Guarded.du_fmap'8314'_154
                  (coe d_injB_96 (coe v1) (coe v4))
                  (coe
                     d_opCall'8314'_854 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84 (coe v1))
                     (coe MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88 (coe v1))
                     (coe d_prjB_128 (coe v0) (coe v3) (coe v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
