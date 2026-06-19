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

module MAlonzo.Code.Once.Arith.SigOp.Builders where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Type

-- Once.Arith.SigOp.Builders.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_10
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_634
-- Once.Arith.SigOp.Builders.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_12 = erased
-- Once.Arith.SigOp.Builders.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_14 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_14 = erased
-- Once.Arith.SigOp.Builders.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_16 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_16
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_598
-- Once.Arith.SigOp.Builders.M.coerce-functor
d_coerce'45'functor_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_94 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_20 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_20 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
      v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-round-trip
d_coerce'45'round'45'trip_22 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_22 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct
d_coerce'45'struct_24 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_24
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_266
-- Once.Arith.SigOp.Builders.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_26 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_26 = erased
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_28 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_28
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_272
-- Once.Arith.SigOp.Builders.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_30 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_30 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ-in
d_coerce'45'μ'45'in_32 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_32 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_746 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-μ-out
d_coerce'45'μ'45'out_34 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_34 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788 v0 v1
      v3
-- Once.Arith.SigOp.Builders.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_36 = erased
-- Once.Arith.SigOp.Builders.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_38 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_38 = erased
-- Once.Arith.SigOp.Builders.M.coerce-ν-in
d_coerce'45'ν'45'in_40 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_40
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_980
-- Once.Arith.SigOp.Builders.M.coerce-ν-out
d_coerce'45'ν'45'out_42 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_42
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_986
-- Once.Arith.SigOp.Builders.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_44 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_44 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_46 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_46 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_48 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_48 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_50 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_50 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_52 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_52 = erased
-- Once.Arith.SigOp.Builders.M.sem-CoIn
d_sem'45'CoIn_54 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_54
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1000
-- Once.Arith.SigOp.Builders.M.sem-CoOut
d_sem'45'CoOut_56 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_56
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_990
-- Once.Arith.SigOp.Builders.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_58 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_58 = erased
-- Once.Arith.SigOp.Builders.M.sem-In
d_sem'45'In_60 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_60
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_920
-- Once.Arith.SigOp.Builders.M.sem-In-Out
d_sem'45'In'45'Out_62 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_62 = erased
-- Once.Arith.SigOp.Builders.M.sem-Out
d_sem'45'Out_64 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_64
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_928
-- Once.Arith.SigOp.Builders.M.sem-Out-In
d_sem'45'Out'45'In_66 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_66 = erased
-- Once.Arith.SigOp.Builders.M.sem-ana
d_sem'45'ana_68 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_68 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1024 v0 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-case
d_sem'45'case_70 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_70 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_330 v3 v4 v5
-- Once.Arith.SigOp.Builders.M.sem-case-inl
d_sem'45'case'45'inl_72 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_72 = erased
-- Once.Arith.SigOp.Builders.M.sem-case-inr
d_sem'45'case'45'inr_74 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_74 = erased
-- Once.Arith.SigOp.Builders.M.sem-cata
d_sem'45'cata_76 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_76 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_940 v0 v1 v3
-- Once.Arith.SigOp.Builders.M.sem-cata-compute
d_sem'45'cata'45'compute_78 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_78 = erased
-- Once.Arith.SigOp.Builders.M.sem-fmap
d_sem'45'fmap_80 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_80 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_418 v0 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-fmap-Type
d_sem'45'fmap'45'Type_82 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_82 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_462 v0 v3
      v4
-- Once.Arith.SigOp.Builders.M.sem-fst
d_sem'45'fst_84 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_84 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_294 v2
-- Once.Arith.SigOp.Builders.M.sem-fst-pair
d_sem'45'fst'45'pair_86 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_86 = erased
-- Once.Arith.SigOp.Builders.M.sem-functor-coherence
d_sem'45'functor'45'coherence_88 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_88 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat
d_sem'45'fuseNat_90 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_90 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1154 v0 v1 v2
      v3 v5 v6
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_92 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
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
d_sem'45'fuseNat'45'cong_92 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_94 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_94 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1250
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.Builders.M.sem-inl
d_sem'45'inl_96 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_96 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_316
-- Once.Arith.SigOp.Builders.M.sem-inr
d_sem'45'inr_98 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_98 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_322
-- Once.Arith.SigOp.Builders.M.sem-pair
d_sem'45'pair_100 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_100 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_306 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-para
d_sem'45'para_102 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_102 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_956 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-snd
d_sem'45'snd_104 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_104 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_300 v2
-- Once.Arith.SigOp.Builders.M.sem-snd-pair
d_sem'45'snd'45'pair_106 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_106 = erased
-- Once.Arith.SigOp.Builders.M.sfmapSemAna
d_sfmapSemAna_108 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_108 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1032 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_110 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_110 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧
d_'10214'_'10215'_112 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_112 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧F
d_'10214'_'10215'F_114 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_114 = erased
-- Once.Arith.SigOp.Builders.M.⟦μ⟧
d_'10214'μ'10215'_116 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_116 = erased
-- Once.Arith.SigOp.Builders.M.⟦ν⟧
d_'10214'ν'10215'_118 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_118 = erased
-- Once.Arith.SigOp.Builders.add-semM
d_add'45'semM_120 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_add'45'semM_120 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe addInt (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.sub-semM
d_sub'45'semM_126 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_sub'45'semM_126 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.mul-semM
d_mul'45'semM_132 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_mul'45'semM_132 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe mulInt (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.neg-semM
d_neg'45'semM_138 :: Integer -> Integer
d_neg'45'semM_138 ~v0 = du_neg'45'semM_138
du_neg'45'semM_138 :: Integer
du_neg'45'semM_138 = coe (0 :: Integer)
-- Once.Arith.SigOp.Builders.div-semM
d_div'45'semM_140
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.div-semM"
-- Once.Arith.SigOp.Builders.mod-semM
d_mod'45'semM_142
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.mod-semM"
-- Once.Arith.SigOp.Builders.lt-semM
d_lt'45'semM_144
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.lt-semM"
-- Once.Arith.SigOp.Builders.le-semM
d_le'45'semM_146
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.le-semM"
-- Once.Arith.SigOp.Builders.gt-semM
d_gt'45'semM_148
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.gt-semM"
-- Once.Arith.SigOp.Builders.ge-semM
d_ge'45'semM_150
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ge-semM"
-- Once.Arith.SigOp.Builders.eq-semM
d_eq'45'semM_152
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.eq-semM"
-- Once.Arith.SigOp.Builders.ne-semM
d_ne'45'semM_154
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ne-semM"
-- Once.Arith.SigOp.Builders.str-lit-semM
d_str'45'lit'45'semM_156 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_str'45'lit'45'semM_156 v0 ~v1 = du_str'45'lit'45'semM_156 v0
du_str'45'lit'45'semM_156 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_str'45'lit'45'semM_156 v0 = coe v0
-- Once.Arith.SigOp.Builders.add-info
d_add'45'info_160 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_add'45'info_160
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.add.int" :: Data.Text.Text)) (coe d_add'45'semM_120)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.sub-info
d_sub'45'info_162 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_sub'45'info_162
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.sub.int" :: Data.Text.Text)) (coe d_sub'45'semM_126)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.mul-info
d_mul'45'info_164 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_mul'45'info_164
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.mul.int" :: Data.Text.Text)) (coe d_mul'45'semM_132)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.div-info
d_div'45'info_166 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_div'45'info_166
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.div.int" :: Data.Text.Text)) (coe d_div'45'semM_140)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.mod-info
d_mod'45'info_168 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_mod'45'info_168
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.mod.int" :: Data.Text.Text)) (coe d_mod'45'semM_142)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.neg-info
d_neg'45'info_170 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_neg'45'info_170
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.neg.int" :: Data.Text.Text))
      (\ v0 -> coe du_neg'45'semM_138)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.lt-info
d_lt'45'info_172 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_lt'45'info_172
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.lt.int" :: Data.Text.Text)) (coe d_lt'45'semM_144)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.le-info
d_le'45'info_174 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_le'45'info_174
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.le.int" :: Data.Text.Text)) (coe d_le'45'semM_146)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.gt-info
d_gt'45'info_176 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_gt'45'info_176
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.gt.int" :: Data.Text.Text)) (coe d_gt'45'semM_148)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.ge-info
d_ge'45'info_178 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_ge'45'info_178
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.ge.int" :: Data.Text.Text)) (coe d_ge'45'semM_150)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.eq-info
d_eq'45'info_180 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_eq'45'info_180
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.eq.int" :: Data.Text.Text)) (coe d_eq'45'semM_152)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.ne-info
d_ne'45'info_182 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_ne'45'info_182
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe ("arith.ne.int" :: Data.Text.Text)) (coe d_ne'45'semM_154)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.str-lit-info
d_str'45'lit'45'info_184 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_str'45'lit'45'info_184 v0
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("lit.str." :: Data.Text.Text) v0)
      (coe (\ v1 -> v0))
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.generic-semM
d_generic'45'semM_192
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.generic-semM"
-- Once.Arith.SigOp.Builders.classify-name
d_classify'45'name_196 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_122
d_classify'45'name_196 v0 v1
  = let v2 = coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> case coe v1 of
                l | (==) l ("linux.exit" :: Data.Text.Text) ->
                    coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_130
                _ -> coe v2
         _ -> coe v2)
-- Once.Arith.SigOp.Builders.generic-info
d_generic'45'info_202 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_generic'45'info_202 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154 (coe v2)
      (coe d_generic'45'semM_192 v0 v1 v2)
      (coe d_classify'45'name_196 (coe v1) (coe v2))
-- Once.Arith.SigOp.Builders.value-info
d_value'45'info_210 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_value'45'info_210 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_154 (coe v2)
      (coe d_generic'45'semM_192 v0 v1 v2)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_126)
-- Once.Arith.SigOp.Builders.arrow-info
d_arrow'45'info_218 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
d_arrow'45'info_218 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> coe d_value'45'info_210 (coe v0) (coe v1) (coe v3)
             MAlonzo.Code.Once.Type.C_eff_36
               -> coe d_generic'45'info_202 (coe v0) (coe v1) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
