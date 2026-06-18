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
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type

-- Once.Arith.SigOp.Builders.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_10
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_648
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
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_612
-- Once.Arith.SigOp.Builders.M.coerce-functor
d_coerce'45'functor_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_20 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_20 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
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
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_280
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
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_286
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
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_760 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-μ-out
d_coerce'45'μ'45'out_34 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_34 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_802 v0 v1 v3
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
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_994
-- Once.Arith.SigOp.Builders.M.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_42 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_42 = erased
-- Once.Arith.SigOp.Builders.M.coerce-ν-out
d_coerce'45'ν'45'out_44 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_44
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_1000
-- Once.Arith.SigOp.Builders.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_46 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_46 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_48 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_48 = erased
-- Once.Arith.SigOp.Builders.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_50 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_50 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_52 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_52 = erased
-- Once.Arith.SigOp.Builders.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_54 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_54 = erased
-- Once.Arith.SigOp.Builders.M.funext
d_funext_56 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funext_56 = erased
-- Once.Arith.SigOp.Builders.M.sem-CoIn
d_sem'45'CoIn_58 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_198
d_sem'45'CoIn_58
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1014
-- Once.Arith.SigOp.Builders.M.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_60 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_60 = erased
-- Once.Arith.SigOp.Builders.M.sem-CoOut
d_sem'45'CoOut_62 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 -> AgdaAny
d_sem'45'CoOut_62
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1004
-- Once.Arith.SigOp.Builders.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_64 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_64 = erased
-- Once.Arith.SigOp.Builders.M.sem-In
d_sem'45'In_66 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_182
d_sem'45'In_66
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_934
-- Once.Arith.SigOp.Builders.M.sem-In-Out
d_sem'45'In'45'Out_68 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_68 = erased
-- Once.Arith.SigOp.Builders.M.sem-Out
d_sem'45'Out_70 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'Out_70
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_942
-- Once.Arith.SigOp.Builders.M.sem-Out-In
d_sem'45'Out'45'In_72 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_72 = erased
-- Once.Arith.SigOp.Builders.M.sem-ana
d_sem'45'ana_74 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_198
d_sem'45'ana_74 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114 v0 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_76 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_76 = erased
-- Once.Arith.SigOp.Builders.M.sem-ana-bisim-anaS
d_sem'45'ana'45'bisim'45'anaS_78 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__1016
d_sem'45'ana'45'bisim'45'anaS_78 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana'45'bisim'45'anaS_1648
      v0 v2
-- Once.Arith.SigOp.Builders.M.sem-ana-is-anaS-unfoldS
d_sem'45'ana'45'is'45'anaS'45'unfoldS_80 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'is'45'anaS'45'unfoldS_80 = erased
-- Once.Arith.SigOp.Builders.M.sem-case
d_sem'45'case_82 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_82 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_344 v3 v4 v5
-- Once.Arith.SigOp.Builders.M.sem-case-inl
d_sem'45'case'45'inl_84 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_84 = erased
-- Once.Arith.SigOp.Builders.M.sem-case-inr
d_sem'45'case'45'inr_86 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_86 = erased
-- Once.Arith.SigOp.Builders.M.sem-cata
d_sem'45'cata_88 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'cata_88 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v0 v1 v3
-- Once.Arith.SigOp.Builders.M.sem-cata-In-id
d_sem'45'cata'45'In'45'id_90 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_90 = erased
-- Once.Arith.SigOp.Builders.M.sem-cata-compute
d_sem'45'cata'45'compute_92 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_92 = erased
-- Once.Arith.SigOp.Builders.M.sem-fmap
d_sem'45'fmap_94 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_94 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 v0 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-fmap-Type
d_sem'45'fmap'45'Type_96 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_96 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_476 v0 v3
      v4
-- Once.Arith.SigOp.Builders.M.sem-fst
d_sem'45'fst_98 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_98 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_308 v2
-- Once.Arith.SigOp.Builders.M.sem-fst-pair
d_sem'45'fst'45'pair_100 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_100 = erased
-- Once.Arith.SigOp.Builders.M.sem-functor-coherence
d_sem'45'functor'45'coherence_102 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_102 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat
d_sem'45'fuseNat_104 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_104 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1244 v0 v1 v2 v3
      v5 v6
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_106 ::
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
  MAlonzo.Code.Once.Functor.Base.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fuseNat'45'cong_106 = erased
-- Once.Arith.SigOp.Builders.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_108 ::
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
  MAlonzo.Code.Once.Functor.Base.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_108 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat'45'events_1340
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.Builders.M.sem-inl
d_sem'45'inl_110 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_110 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_330
-- Once.Arith.SigOp.Builders.M.sem-inr
d_sem'45'inr_112 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_112 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_336
-- Once.Arith.SigOp.Builders.M.sem-pair
d_sem'45'pair_114 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_114 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-para
d_sem'45'para_116 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'para_116 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_970 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-snd
d_sem'45'snd_118 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_118 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_314 v2
-- Once.Arith.SigOp.Builders.M.sem-snd-pair
d_sem'45'snd'45'pair_120 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_120 = erased
-- Once.Arith.SigOp.Builders.M.sfmap-bisim
d_sfmap'45'bisim_122 ::
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_198) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_198) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__1016) ->
  AgdaAny -> AgdaAny
d_sfmap'45'bisim_122 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmap'45'bisim_1586 v0 v4 v5
-- Once.Arith.SigOp.Builders.M.sfmapSemAna
d_sfmapSemAna_124 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_124 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmapSemAna_1122 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_126 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_126 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧
d_'10214'_'10215'_128 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_128 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧F
d_'10214'_'10215'F_130 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_130 = erased
-- Once.Arith.SigOp.Builders.M.⟦μ⟧
d_'10214'μ'10215'_132 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_132 = erased
-- Once.Arith.SigOp.Builders.M.⟦ν⟧
d_'10214'ν'10215'_134 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_134 = erased
-- Once.Arith.SigOp.Builders.add-semM
d_add'45'semM_136 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_add'45'semM_136 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe addInt (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.sub-semM
d_sub'45'semM_142 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_sub'45'semM_142 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.mul-semM
d_mul'45'semM_148 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_mul'45'semM_148 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe mulInt (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.neg-semM
d_neg'45'semM_154 :: Integer -> Integer
d_neg'45'semM_154 ~v0 = du_neg'45'semM_154
du_neg'45'semM_154 :: Integer
du_neg'45'semM_154 = coe (0 :: Integer)
-- Once.Arith.SigOp.Builders.div-semM
d_div'45'semM_156
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.div-semM"
-- Once.Arith.SigOp.Builders.mod-semM
d_mod'45'semM_158
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.mod-semM"
-- Once.Arith.SigOp.Builders.lt-semM
d_lt'45'semM_160
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.lt-semM"
-- Once.Arith.SigOp.Builders.le-semM
d_le'45'semM_162
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.le-semM"
-- Once.Arith.SigOp.Builders.gt-semM
d_gt'45'semM_164
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.gt-semM"
-- Once.Arith.SigOp.Builders.ge-semM
d_ge'45'semM_166
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ge-semM"
-- Once.Arith.SigOp.Builders.eq-semM
d_eq'45'semM_168
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.eq-semM"
-- Once.Arith.SigOp.Builders.ne-semM
d_ne'45'semM_170
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.ne-semM"
-- Once.Arith.SigOp.Builders.str-lit-semM
d_str'45'lit'45'semM_172 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_str'45'lit'45'semM_172 v0 ~v1 = du_str'45'lit'45'semM_172 v0
du_str'45'lit'45'semM_172 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_str'45'lit'45'semM_172 v0 = coe v0
-- Once.Arith.SigOp.Builders.add-info
d_add'45'info_176 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_add'45'info_176
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.add.int" :: Data.Text.Text)) (coe d_add'45'semM_136)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.sub-info
d_sub'45'info_178 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_sub'45'info_178
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.sub.int" :: Data.Text.Text)) (coe d_sub'45'semM_142)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.mul-info
d_mul'45'info_180 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_mul'45'info_180
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.mul.int" :: Data.Text.Text)) (coe d_mul'45'semM_148)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.div-info
d_div'45'info_182 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_div'45'info_182
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.div.int" :: Data.Text.Text)) (coe d_div'45'semM_156)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.mod-info
d_mod'45'info_184 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_mod'45'info_184
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.mod.int" :: Data.Text.Text)) (coe d_mod'45'semM_158)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.neg-info
d_neg'45'info_186 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_neg'45'info_186
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.neg.int" :: Data.Text.Text))
      (\ v0 -> coe du_neg'45'semM_154)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.lt-info
d_lt'45'info_188 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_lt'45'info_188
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.lt.int" :: Data.Text.Text)) (coe d_lt'45'semM_160)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.le-info
d_le'45'info_190 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_le'45'info_190
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.le.int" :: Data.Text.Text)) (coe d_le'45'semM_162)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.gt-info
d_gt'45'info_192 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_gt'45'info_192
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.gt.int" :: Data.Text.Text)) (coe d_gt'45'semM_164)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.ge-info
d_ge'45'info_194 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_ge'45'info_194
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.ge.int" :: Data.Text.Text)) (coe d_ge'45'semM_166)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.eq-info
d_eq'45'info_196 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_eq'45'info_196
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.eq.int" :: Data.Text.Text)) (coe d_eq'45'semM_168)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.ne-info
d_ne'45'info_198 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_ne'45'info_198
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe ("arith.ne.int" :: Data.Text.Text)) (coe d_ne'45'semM_170)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.str-lit-info
d_str'45'lit'45'info_200 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_str'45'lit'45'info_200 v0
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("lit.str." :: Data.Text.Text) v0)
      (coe (\ v1 -> v0))
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.generic-semM
d_generic'45'semM_208
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Arith.SigOp.Builders.generic-semM"
-- Once.Arith.SigOp.Builders.classify-name
d_classify'45'name_212 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_138
d_classify'45'name_212 v0 v1
  = let v2 = coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> case coe v1 of
                l | (==) l ("linux.exit" :: Data.Text.Text) ->
                    coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_146
                _ -> coe v2
         _ -> coe v2)
-- Once.Arith.SigOp.Builders.generic-info
d_generic'45'info_218 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_generic'45'info_218 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170 (coe v2)
      (coe d_generic'45'semM_208 v0 v1 v2)
      (coe d_classify'45'name_212 (coe v1) (coe v2))
-- Once.Arith.SigOp.Builders.value-info
d_value'45'info_226 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_value'45'info_226 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_170 (coe v2)
      (coe d_generic'45'semM_208 v0 v1 v2)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_142)
-- Once.Arith.SigOp.Builders.arrow-info
d_arrow'45'info_234 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_152
d_arrow'45'info_234 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> coe d_value'45'info_226 (coe v0) (coe v1) (coe v3)
             MAlonzo.Code.Once.Type.C_eff_36
               -> coe d_generic'45'info_218 (coe v0) (coe v1) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
