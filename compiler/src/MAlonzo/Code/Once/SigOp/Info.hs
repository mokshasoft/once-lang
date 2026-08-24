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

module MAlonzo.Code.Once.SigOp.Info where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.SigOp.Info.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_636
-- Once.SigOp.Info.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_10 = erased
-- Once.SigOp.Info.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 = erased
-- Once.SigOp.Info.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_14 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_14
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_600
-- Once.SigOp.Info.M.coerce-functor
d_coerce'45'functor_16 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96 v0 v2
-- Once.SigOp.Info.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
      v0 v2
-- Once.SigOp.Info.M.coerce-round-trip
d_coerce'45'round'45'trip_20 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_20 = erased
-- Once.SigOp.Info.M.coerce-struct
d_coerce'45'struct_22 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_22
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_268
-- Once.SigOp.Info.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_24 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_24 = erased
-- Once.SigOp.Info.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_26 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_26
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_274
-- Once.SigOp.Info.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_28 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_28 = erased
-- Once.SigOp.Info.M.coerce-μ-in
d_coerce'45'μ'45'in_30 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_30 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_748 v0 v2
-- Once.SigOp.Info.M.coerce-μ-out
d_coerce'45'μ'45'out_32 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_32 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790 v0 v1
      v3
-- Once.SigOp.Info.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_34 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_34 = erased
-- Once.SigOp.Info.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_36 = erased
-- Once.SigOp.Info.M.coerce-ν-in
d_coerce'45'ν'45'in_38 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_38
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_982
-- Once.SigOp.Info.M.coerce-ν-out
d_coerce'45'ν'45'out_40 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_40
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_988
-- Once.SigOp.Info.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_42 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_42 = erased
-- Once.SigOp.Info.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_44 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_44 = erased
-- Once.SigOp.Info.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_46 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_46 = erased
-- Once.SigOp.Info.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_48 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_48 = erased
-- Once.SigOp.Info.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_50 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_50 = erased
-- Once.SigOp.Info.M.sem-CoIn
d_sem'45'CoIn_52 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_52
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1002
-- Once.SigOp.Info.M.sem-CoOut
d_sem'45'CoOut_54 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_54
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_992
-- Once.SigOp.Info.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_56 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_56 = erased
-- Once.SigOp.Info.M.sem-In
d_sem'45'In_58 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_58
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_922
-- Once.SigOp.Info.M.sem-In-Out
d_sem'45'In'45'Out_60 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_60 = erased
-- Once.SigOp.Info.M.sem-Out
d_sem'45'Out_62 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_62
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_930
-- Once.SigOp.Info.M.sem-Out-In
d_sem'45'Out'45'In_64 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_64 = erased
-- Once.SigOp.Info.M.sem-ana
d_sem'45'ana_66 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_66 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1026 v0 v2 v3
-- Once.SigOp.Info.M.sem-case
d_sem'45'case_68 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_68 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_332 v3 v4 v5
-- Once.SigOp.Info.M.sem-case-inl
d_sem'45'case'45'inl_70 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_70 = erased
-- Once.SigOp.Info.M.sem-case-inr
d_sem'45'case'45'inr_72 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_72 = erased
-- Once.SigOp.Info.M.sem-cata
d_sem'45'cata_74 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_74 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942 v0 v1 v3
-- Once.SigOp.Info.M.sem-cata-compute
d_sem'45'cata'45'compute_76 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_76 = erased
-- Once.SigOp.Info.M.sem-fmap
d_sem'45'fmap_78 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_78 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 v0 v3 v4
-- Once.SigOp.Info.M.sem-fmap-Type
d_sem'45'fmap'45'Type_80 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_80 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_464 v0 v3
      v4
-- Once.SigOp.Info.M.sem-fst
d_sem'45'fst_82 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_82 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_296 v2
-- Once.SigOp.Info.M.sem-fst-pair
d_sem'45'fst'45'pair_84 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_84 = erased
-- Once.SigOp.Info.M.sem-functor-coherence
d_sem'45'functor'45'coherence_86 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_86 = erased
-- Once.SigOp.Info.M.sem-fuseNat
d_sem'45'fuseNat_88 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_88 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1156 v0 v1 v2
      v3 v5 v6
-- Once.SigOp.Info.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_90 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (() ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fuseNat'45'cong_90 = erased
-- Once.SigOp.Info.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_92 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_92 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1252
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.SigOp.Info.M.sem-inl
d_sem'45'inl_94 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_94 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_318
-- Once.SigOp.Info.M.sem-inr
d_sem'45'inr_96 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_96 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_324
-- Once.SigOp.Info.M.sem-pair
d_sem'45'pair_98 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_98 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_308 v2 v3
-- Once.SigOp.Info.M.sem-para
d_sem'45'para_100 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_100 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_958 v0 v1 v3 v4
-- Once.SigOp.Info.M.sem-snd
d_sem'45'snd_102 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_102 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_302 v2
-- Once.SigOp.Info.M.sem-snd-pair
d_sem'45'snd'45'pair_104 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_104 = erased
-- Once.SigOp.Info.M.sfmapSemAna
d_sfmapSemAna_106 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_106 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1034 v0 v1 v3 v4
-- Once.SigOp.Info.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_108 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_108 = erased
-- Once.SigOp.Info.M.⟦_⟧
d_'10214'_'10215'_110 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_110 = erased
-- Once.SigOp.Info.M.⟦_⟧F
d_'10214'_'10215'F_112 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_112 = erased
-- Once.SigOp.Info.M.⟦μ⟧
d_'10214'μ'10215'_114 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_114 = erased
-- Once.SigOp.Info.M.⟦ν⟧
d_'10214'ν'10215'_116 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_116 = erased
-- Once.SigOp.Info.EffectShape
d_EffectShape_120 a0 = ()
data T_EffectShape_120 = C_Pure_124 | C_Emits_126 | C_Halts_128
-- Once.SigOp.Info.SigOpSem
d_SigOpSem_134 a0 a1 = ()
data T_SigOpSem_134
  = C_pureV_140 (MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
                 AgdaAny -> AgdaAny) |
    C_emitsV_142 | C_haltsV_144
-- Once.SigOp.Info.Linkage
d_Linkage_148 a0 = ()
data T_Linkage_148
  = C_ffi'45'concrete_152 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_internal'45'ref_154
-- Once.SigOp.Info.SigOpInfo
d_SigOpInfo_160 a0 a1 = ()
data T_SigOpInfo_160
  = C_mk'45'info''_182 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                       T_SigOpSem_134 MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
                       T_Linkage_148
-- Once.SigOp.Info.SigOpInfo.name
d_name_174 ::
  T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_name_174 v0
  = case coe v0 of
      C_mk'45'info''_182 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.sem
d_sem_176 :: T_SigOpInfo_160 -> T_SigOpSem_134
d_sem_176 v0
  = case coe v0 of
      C_mk'45'info''_182 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.baseA
d_baseA_178 ::
  T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_baseA_178 v0
  = case coe v0 of
      C_mk'45'info''_182 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.conB
d_conB_180 :: T_SigOpInfo_160 -> T_Linkage_148
d_conB_180 v0
  = case coe v0 of
      C_mk'45'info''_182 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.semM
d_semM_188 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> AgdaAny -> AgdaAny
d_semM_188 ~v0 ~v1 v2 = du_semM_188 v2
du_semM_188 ::
  T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> AgdaAny -> AgdaAny
du_semM_188 v0 = coe du_go_200 (coe d_sem_176 (coe v0))
-- Once.SigOp.Info._.go
d_go_200 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_SigOpSem_134 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> AgdaAny -> AgdaAny
d_go_200 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_go_200 v5
du_go_200 ::
  T_SigOpSem_134 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> AgdaAny -> AgdaAny
du_go_200 v0
  = case coe v0 of
      C_pureV_140 v1 -> coe v1
      C_emitsV_142
        -> coe (\ v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_haltsV_144
        -> coe (\ v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.effect
d_effect_216 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_SigOpInfo_160 -> T_EffectShape_120
d_effect_216 ~v0 ~v1 v2 = du_effect_216 v2
du_effect_216 :: T_SigOpInfo_160 -> T_EffectShape_120
du_effect_216 v0 = coe du_go_228 (coe d_sem_176 (coe v0))
-- Once.SigOp.Info._.go
d_go_228 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_SigOpSem_134 -> T_EffectShape_120
d_go_228 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_go_228 v5
du_go_228 :: T_SigOpSem_134 -> T_EffectShape_120
du_go_228 v0
  = case coe v0 of
      C_pureV_140 v1 -> coe C_Pure_124
      C_emitsV_142 -> coe C_Emits_126
      C_haltsV_144 -> coe C_Halts_128
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.mk-info
d_mk'45'info_238 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
   AgdaAny -> AgdaAny) ->
  T_EffectShape_120 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  T_SigOpInfo_160
d_mk'45'info_238 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_mk'45'info_238 v2 v3 v4 v5 v6
du_mk'45'info_238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
   AgdaAny -> AgdaAny) ->
  T_EffectShape_120 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  T_SigOpInfo_160
du_mk'45'info_238 v0 v1 v2 v3 v4
  = case coe v2 of
      C_Pure_124
        -> coe
             C_mk'45'info''_182 (coe v0) (coe C_pureV_140 (coe v1)) (coe v3)
             (coe C_ffi'45'concrete_152 (coe v4))
      C_Emits_126
        -> coe
             C_mk'45'info''_182 (coe v0) (coe C_emitsV_142) (coe v3)
             (coe C_ffi'45'concrete_152 (coe v4))
      C_Halts_128
        -> coe
             C_mk'45'info''_182 (coe v0) (coe C_haltsV_144) (coe v3)
             (coe C_ffi'45'concrete_152 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info._≟SigOpInfo-name_
d__'8799'SigOpInfo'45'name__276 ::
  T_SigOpInfo_160 ->
  T_SigOpInfo_160 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'SigOpInfo'45'name__276 v0 v1
  = coe
      MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__16
      (coe d_name_174 (coe v0)) (coe d_name_174 (coe v1))
-- Once.SigOp.Info.sigOpInfo-name-coherence
d_sigOpInfo'45'name'45'coherence_290
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SigOp.Info.sigOpInfo-name-coherence"
-- Once.SigOp.Info._≟SigOpInfo_
d__'8799'SigOpInfo__300 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_SigOpInfo_160 ->
  T_SigOpInfo_160 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'SigOpInfo__300 ~v0 ~v1 v2 v3
  = du__'8799'SigOpInfo__300 v2 v3
du__'8799'SigOpInfo__300 ::
  T_SigOpInfo_160 ->
  T_SigOpInfo_160 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'SigOpInfo__300 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
              (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54)
              (coe
                 MAlonzo.Code.Once.CanonicalName.d_parts_8
                 (coe d_name_174 (coe v0)))
              (coe
                 MAlonzo.Code.Once.CanonicalName.d_parts_8
                 (coe d_name_174 (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then let v5
                           = seq
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe v3)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                            -> if coe v6
                                 then coe
                                        seq (coe v7)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v6)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                              erased))
                                 else coe
                                        seq (coe v7)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v6)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else (let v5
                            = seq
                                (coe v4)
                                (coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                   (coe v3)
                                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                             -> if coe v6
                                  then coe
                                         seq (coe v7)
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe v6)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                               erased))
                                  else coe
                                         seq (coe v7)
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe v6)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
