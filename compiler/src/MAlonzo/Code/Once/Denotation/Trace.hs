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

module MAlonzo.Code.Once.Denotation.Trace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Denotation.Trace.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_648
-- Once.Denotation.Trace.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_10 = erased
-- Once.Denotation.Trace.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 = erased
-- Once.Denotation.Trace.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_14 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_14
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_612
-- Once.Denotation.Trace.M.coerce-functor
d_coerce'45'functor_16 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 v0 v2
-- Once.Denotation.Trace.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      v0 v2
-- Once.Denotation.Trace.M.coerce-round-trip
d_coerce'45'round'45'trip_20 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_20 = erased
-- Once.Denotation.Trace.M.coerce-struct
d_coerce'45'struct_22 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_22
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_280
-- Once.Denotation.Trace.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_24 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_24 = erased
-- Once.Denotation.Trace.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_26 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_26
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_286
-- Once.Denotation.Trace.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_28 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_28 = erased
-- Once.Denotation.Trace.M.coerce-μ-in
d_coerce'45'μ'45'in_30 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_30 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_760 v0 v2
-- Once.Denotation.Trace.M.coerce-μ-out
d_coerce'45'μ'45'out_32 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_32 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_802 v0 v1 v3
-- Once.Denotation.Trace.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_34 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_34 = erased
-- Once.Denotation.Trace.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_36 = erased
-- Once.Denotation.Trace.M.coerce-ν-in
d_coerce'45'ν'45'in_38 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_38
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_994
-- Once.Denotation.Trace.M.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_40 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_40 = erased
-- Once.Denotation.Trace.M.coerce-ν-out
d_coerce'45'ν'45'out_42 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_42
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_1000
-- Once.Denotation.Trace.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_44 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_44 = erased
-- Once.Denotation.Trace.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_46 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_46 = erased
-- Once.Denotation.Trace.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_48 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_48 = erased
-- Once.Denotation.Trace.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_50 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_50 = erased
-- Once.Denotation.Trace.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_52 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_52 = erased
-- Once.Denotation.Trace.M.funext
d_funext_54 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funext_54 = erased
-- Once.Denotation.Trace.M.sem-CoIn
d_sem'45'CoIn_56 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_198
d_sem'45'CoIn_56
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1014
-- Once.Denotation.Trace.M.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_58 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_58 = erased
-- Once.Denotation.Trace.M.sem-CoOut
d_sem'45'CoOut_60 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 -> AgdaAny
d_sem'45'CoOut_60
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1004
-- Once.Denotation.Trace.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_62 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_62 = erased
-- Once.Denotation.Trace.M.sem-In
d_sem'45'In_64 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_182
d_sem'45'In_64
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_934
-- Once.Denotation.Trace.M.sem-In-Out
d_sem'45'In'45'Out_66 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_66 = erased
-- Once.Denotation.Trace.M.sem-Out
d_sem'45'Out_68 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'Out_68
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_942
-- Once.Denotation.Trace.M.sem-Out-In
d_sem'45'Out'45'In_70 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_70 = erased
-- Once.Denotation.Trace.M.sem-ana
d_sem'45'ana_72 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_198
d_sem'45'ana_72 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114 v0 v2 v3
-- Once.Denotation.Trace.M.sem-ana-Out-bisim
d_sem'45'ana'45'Out'45'bisim_74 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__1016
d_sem'45'ana'45'Out'45'bisim_74 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana'45'Out'45'bisim_1630
      v0 v1 v2 v3
-- Once.Denotation.Trace.M.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_76 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_76 = erased
-- Once.Denotation.Trace.M.sem-ana-Out-rel
d_sem'45'ana'45'Out'45'rel_78 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_sem'45'ana'45'Out'45'rel_78
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana'45'Out'45'rel_1642
-- Once.Denotation.Trace.M.sem-case
d_sem'45'case_80 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_80 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_344 v3 v4 v5
-- Once.Denotation.Trace.M.sem-case-inl
d_sem'45'case'45'inl_82 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_82 = erased
-- Once.Denotation.Trace.M.sem-case-inr
d_sem'45'case'45'inr_84 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_84 = erased
-- Once.Denotation.Trace.M.sem-cata
d_sem'45'cata_86 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'cata_86 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v0 v1 v3
-- Once.Denotation.Trace.M.sem-cata-In-id
d_sem'45'cata'45'In'45'id_88 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_88 = erased
-- Once.Denotation.Trace.M.sem-cata-compute
d_sem'45'cata'45'compute_90 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_90 = erased
-- Once.Denotation.Trace.M.sem-fmap
d_sem'45'fmap_92 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_92 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 v0 v3 v4
-- Once.Denotation.Trace.M.sem-fmap-Type
d_sem'45'fmap'45'Type_94 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_94 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_476 v0 v3
      v4
-- Once.Denotation.Trace.M.sem-fst
d_sem'45'fst_96 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_96 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_308 v2
-- Once.Denotation.Trace.M.sem-fst-pair
d_sem'45'fst'45'pair_98 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_98 = erased
-- Once.Denotation.Trace.M.sem-functor-coherence
d_sem'45'functor'45'coherence_100 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_100 = erased
-- Once.Denotation.Trace.M.sem-fuseNat
d_sem'45'fuseNat_102 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_102 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1244 v0 v1 v2 v3
      v5 v6
-- Once.Denotation.Trace.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_104 ::
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
d_sem'45'fuseNat'45'cong_104 = erased
-- Once.Denotation.Trace.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_106 ::
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
d_sem'45'fuseNat'45'events_106 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat'45'events_1340
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Denotation.Trace.M.sem-inl
d_sem'45'inl_108 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_108 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_330
-- Once.Denotation.Trace.M.sem-inr
d_sem'45'inr_110 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_110 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_336
-- Once.Denotation.Trace.M.sem-pair
d_sem'45'pair_112 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_112 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320 v2 v3
-- Once.Denotation.Trace.M.sem-para
d_sem'45'para_114 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'para_114 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_970 v0 v1 v3 v4
-- Once.Denotation.Trace.M.sem-snd
d_sem'45'snd_116 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_116 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_314 v2
-- Once.Denotation.Trace.M.sem-snd-pair
d_sem'45'snd'45'pair_118 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_118 = erased
-- Once.Denotation.Trace.M.sfmapSemAna
d_sfmapSemAna_120 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_120 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmapSemAna_1122 v0 v1 v3 v4
-- Once.Denotation.Trace.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_122 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_122 = erased
-- Once.Denotation.Trace.M.⟦_⟧
d_'10214'_'10215'_124 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_124 = erased
-- Once.Denotation.Trace.M.⟦_⟧F
d_'10214'_'10215'F_126 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_126 = erased
-- Once.Denotation.Trace.M.⟦μ⟧
d_'10214'μ'10215'_128 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_128 = erased
-- Once.Denotation.Trace.M.⟦ν⟧
d_'10214'ν'10215'_130 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_130 = erased
-- Once.Denotation.Trace.isInt?
d_isInt'63'_134 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isInt'63'_134 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Int_136
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
         _ -> coe v1)
-- Once.Denotation.Trace.SigOpEvent
d_SigOpEvent_136 = ()
data T_SigOpEvent_136
  = C_mk'45'event_146 MAlonzo.Code.Agda.Builtin.String.T_String_6
                      (Maybe Integer)
-- Once.Denotation.Trace.SigOpEvent.ev-name
d_ev'45'name_142 ::
  T_SigOpEvent_136 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_ev'45'name_142 v0
  = case coe v0 of
      C_mk'45'event_146 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Trace.SigOpEvent.ev-argℕ
d_ev'45'argℕ_144 :: T_SigOpEvent_136 -> Maybe Integer
d_ev'45'argℕ_144 v0
  = case coe v0 of
      C_mk'45'event_146 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Trace.mkEvent
d_mkEvent_152 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_150 ->
  AgdaAny -> T_SigOpEvent_136
d_mkEvent_152 v0 ~v1 v2 v3 = du_mkEvent_152 v0 v2 v3
du_mkEvent_152 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_150 ->
  AgdaAny -> T_SigOpEvent_136
du_mkEvent_152 v0 v1 v2
  = let v3 = d_isInt'63'_134 (coe v0) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                C_mk'45'event_146
                (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_162 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                C_mk'45'event_146
                (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_162 (coe v1)) (coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.Trace.exitCodeOf
d_exitCodeOf_176 :: [T_SigOpEvent_136] -> Maybe Integer
d_exitCodeOf_176 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v3 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe d_ev'45'name_142 (coe v1)))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                        (coe d_ev'45'name_142 (coe v1))
                        (coe ("linux.exit" :: Data.Text.Text))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then coe seq (coe v5) (coe d_ev'45'argℕ_144 (coe v1))
                       else coe seq (coe v5) (coe d_exitCodeOf_176 (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
