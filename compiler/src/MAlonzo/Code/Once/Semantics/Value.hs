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

module MAlonzo.Code.Once.Semantics.Value where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.FunctorMeaning
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Semantics.Functor

-- Once.Semantics.Value._.coerce-base-to-full
d_coerce'45'base'45'to'45'full_12 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_12 ~v0 ~v1
  = du_coerce'45'base'45'to'45'full_12
du_coerce'45'base'45'to'45'full_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_12
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_440
-- Once.Semantics.Value._.coerce-full-to-base
d_coerce'45'full'45'to'45'base_14 ::
  () ->
  () -> MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_14 ~v0 ~v1
  = du_coerce'45'full'45'to'45'base_14
du_coerce'45'full'45'to'45'base_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
du_coerce'45'full'45'to'45'base_14
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_408
-- Once.Semantics.Value._.coerce-functor
d_coerce'45'functor_16 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_16 ~v0 ~v1 = du_coerce'45'functor_16
du_coerce'45'functor_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
du_coerce'45'functor_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_282 v0 v2
-- Once.Semantics.Value._.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_18 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_18 ~v0 ~v1
  = du_coerce'45'functor'8315''185'_18
du_coerce'45'functor'8315''185'_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185'_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_324 v0
      v2
-- Once.Semantics.Value._.coerce-μ-in
d_coerce'45'μ'45'in_20 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_20 ~v0 ~v1 = du_coerce'45'μ'45'in_20
du_coerce'45'μ'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'in_20 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_472 v0 v2
-- Once.Semantics.Value._.coerce-μ-out
d_coerce'45'μ'45'out_22 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_22 ~v0 ~v1 = du_coerce'45'μ'45'out_22
du_coerce'45'μ'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'out_22 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_514 v0 v1 v3
-- Once.Semantics.Value._.sem-CoIn
d_sem'45'CoIn_30 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_30 ~v0 ~v1 = du_sem'45'CoIn_30
du_sem'45'CoIn_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
du_sem'45'CoIn_30
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_634
-- Once.Semantics.Value._.sem-CoOut
d_sem'45'CoOut_32 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_32 ~v0 ~v1 = du_sem'45'CoOut_32
du_sem'45'CoOut_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
du_sem'45'CoOut_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_624
-- Once.Semantics.Value._.sem-In
d_sem'45'In_34 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_34 ~v0 ~v1 = du_sem'45'In_34
du_sem'45'In_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
du_sem'45'In_34 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_554
-- Once.Semantics.Value._.sem-Out
d_sem'45'Out_36 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_36 ~v0 ~v1 = du_sem'45'Out_36
du_sem'45'Out_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'Out_36
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_562
-- Once.Semantics.Value._.sem-ana
d_sem'45'ana_38 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_38 ~v0 ~v1 = du_sem'45'ana_38
du_sem'45'ana_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
du_sem'45'ana_38 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_644 v0 v2 v3
-- Once.Semantics.Value._.sem-cata
d_sem'45'cata_40 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_40 ~v0 ~v1 = du_sem'45'cata_40
du_sem'45'cata_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'cata_40 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_574 v0 v1 v3
-- Once.Semantics.Value._.sem-fmap
d_sem'45'fmap_42 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_42 ~v0 ~v1 = du_sem'45'fmap_42
du_sem'45'fmap_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap_42 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_368 v0 v3 v4
-- Once.Semantics.Value._.sfmapSemAna
d_sfmapSemAna_48 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_48 ~v0 ~v1 = du_sfmapSemAna_48
du_sfmapSemAna_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
du_sfmapSemAna_48 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_658 v0 v1 v3 v4
-- Once.Semantics.Value._.⟦_⟧
d_'10214'_'10215'_50 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_50 = erased
-- Once.Semantics.Value._.⟦_⟧F
d_'10214'_'10215'F_52 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_52 = erased
-- Once.Semantics.Value._.⟦μ⟧
d_'10214'μ'10215'_56 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_56 = erased
-- Once.Semantics.Value._.⟦ν⟧
d_'10214'ν'10215'_58 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_58 = erased
-- Once.Semantics.Value.sem-functor-coherence
d_sem'45'functor'45'coherence_64 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_64 = erased
-- Once.Semantics.Value.coerce-round-trip
d_coerce'45'round'45'trip_106 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_106 = erased
-- Once.Semantics.Value.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_150 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_150 = erased
-- Once.Semantics.Value.coerce-struct
d_coerce'45'struct_192 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'struct_192 ~v0 ~v1 = du_coerce'45'struct_192
du_coerce'45'struct_192 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
du_coerce'45'struct_192 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_282 v0 v2
-- Once.Semantics.Value.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_198 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_198 ~v0 ~v1
  = du_coerce'45'struct'8315''185'_198
du_coerce'45'struct'8315''185'_198 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
du_coerce'45'struct'8315''185'_198 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_324 v0
      v2
-- Once.Semantics.Value.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_206 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_206 = erased
-- Once.Semantics.Value.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_214 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_214 = erased
-- Once.Semantics.Value.sem-fst
d_sem'45'fst_220 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_220 ~v0 ~v1 ~v2 ~v3 v4 = du_sem'45'fst_220 v4
du_sem'45'fst_220 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'fst_220 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.Semantics.Value.sem-snd
d_sem'45'snd_226 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_226 ~v0 ~v1 ~v2 ~v3 v4 = du_sem'45'snd_226 v4
du_sem'45'snd_226 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'snd_226 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.Semantics.Value.sem-pair
d_sem'45'pair_232 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_232 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sem'45'pair_232 v4 v5
du_sem'45'pair_232 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'pair_232 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Semantics.Value.sem-inl
d_sem'45'inl_242 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_242 ~v0 ~v1 ~v2 ~v3 = du_sem'45'inl_242
du_sem'45'inl_242 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inl_242 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
-- Once.Semantics.Value.sem-inr
d_sem'45'inr_248 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_248 ~v0 ~v1 ~v2 ~v3 = du_sem'45'inr_248
du_sem'45'inr_248 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inr_248 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
-- Once.Semantics.Value.sem-case
d_sem'45'case_256 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_256 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_sem'45'case_256 v5 v6 v7
du_sem'45'case_256 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_sem'45'case_256 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v0 v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sem-fst-pair
d_sem'45'fst'45'pair_278 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_278 = erased
-- Once.Semantics.Value.sem-snd-pair
d_sem'45'snd'45'pair_292 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_292 = erased
-- Once.Semantics.Value.sem-case-inl
d_sem'45'case'45'inl_310 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_310 = erased
-- Once.Semantics.Value.sem-case-inr
d_sem'45'case'45'inr_330 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_330 = erased
-- Once.Semantics.Value.sem-fmap-Type
d_sem'45'fmap'45'Type_344 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_344 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_sem'45'fmap'45'Type_344 v2 v5 v6
du_sem'45'fmap'45'Type_344 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap'45'Type_344 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v3 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v1 v2
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap'45'Type_344 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap'45'Type_344 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap'45'Type_344 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap'45'Type_344 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.fmap-struct-coherence
d_fmap'45'struct'45'coherence_392 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_392 = erased
-- Once.Semantics.Value.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_440 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_440 = erased
-- Once.Semantics.Value.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_484 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_484 = erased
-- Once.Semantics.Value.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_518 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_518 = erased
-- Once.Semantics.Value.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_554 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_554 = erased
-- Once.Semantics.Value.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_600 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_600 = erased
-- Once.Semantics.Value.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_644 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_644 = erased
-- Once.Semantics.Value.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_662 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_662 = erased
-- Once.Semantics.Value.sem-fuseNat
d_sem'45'fuseNat_718 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'fuseNat_718 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_sem'45'fuseNat_718 v2 v3 v4 v5 v7 v8
du_sem'45'fuseNat_718 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'fuseNat_718 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_fuseNatS_436
      (coe
         MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v1))
      erased
      (coe
         (\ v6 v7 ->
            coe
              MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_472 (coe v0)
              (coe
                 v4 v6
                 (coe
                    MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_514 (coe v1)
                    (coe v3) (coe v7)))))
      (coe
         (\ v6 ->
            coe
              v5
              (coe
                 MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_514 (coe v0)
                 (coe v2) (coe v6))))
-- Once.Semantics.Value.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_762 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (() ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fuseNat'45'cong_762 = erased
-- Once.Semantics.Value._.Φ-eq
d_Φ'45'eq_794 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (() ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Φ'45'eq_794 = erased
-- Once.Semantics.Value.sem-fuseNat-events
d_sem'45'fuseNat'45'events_814 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_814 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9
                               v10 v11
  = du_sem'45'fuseNat'45'events_814 v3 v4 v5 v6 v7 v8 v10 v11
du_sem'45'fuseNat'45'events_814 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'fuseNat'45'events_814 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_fuseNatW_458
      (coe
         MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v2))
      (coe
         MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v3))
      (coe v0) (coe v1)
      (coe
         (\ v8 v9 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
              (coe
                 MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_472 (coe v2)
                 (coe
                    v6 v8
                    (coe
                       MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_514 (coe v3)
                       (coe v5) (coe v9))))))
      (coe
         (\ v8 ->
            coe
              v7
              (coe
                 MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_514 (coe v2)
                 (coe v4) (coe v8))))
-- Once.Semantics.Value.sem-Out-In
d_sem'45'Out'45'In_848 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_848 = erased
-- Once.Semantics.Value.sem-In-Out
d_sem'45'In'45'Out_860 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_860 = erased
-- Once.Semantics.Value.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_876 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_876 = erased
-- Once.Semantics.Value.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_926 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_926 = erased
-- Once.Semantics.Value.sem-cata-compute
d_sem'45'cata'45'compute_974 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_974 = erased
