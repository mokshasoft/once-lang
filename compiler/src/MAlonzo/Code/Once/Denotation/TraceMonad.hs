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

module MAlonzo.Code.Once.Denotation.TraceMonad where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Denotation.TraceMonad.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_786
-- Once.Denotation.TraceMonad.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_10 = erased
-- Once.Denotation.TraceMonad.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 = erased
-- Once.Denotation.TraceMonad.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_14 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_14
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_754
-- Once.Denotation.TraceMonad.M.coerce-functor
d_coerce'45'functor_16 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_250 v0 v2
-- Once.Denotation.TraceMonad.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_18 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_292
      v0 v2
-- Once.Denotation.TraceMonad.M.coerce-round-trip
d_coerce'45'round'45'trip_20 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_20 = erased
-- Once.Denotation.TraceMonad.M.coerce-struct
d_coerce'45'struct_22 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_22
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_422
-- Once.Denotation.TraceMonad.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_24 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_24 = erased
-- Once.Denotation.TraceMonad.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_26 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_26
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_428
-- Once.Denotation.TraceMonad.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_28 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_28 = erased
-- Once.Denotation.TraceMonad.M.coerce-μ-in
d_coerce'45'μ'45'in_30 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_30 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_886 v0 v2
-- Once.Denotation.TraceMonad.M.coerce-μ-out
d_coerce'45'μ'45'out_32 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_32 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928 v0 v1
      v3
-- Once.Denotation.TraceMonad.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_34 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_34 = erased
-- Once.Denotation.TraceMonad.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_36 = erased
-- Once.Denotation.TraceMonad.M.coerce-ν-in
d_coerce'45'ν'45'in_38 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_38
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120
-- Once.Denotation.TraceMonad.M.coerce-ν-out
d_coerce'45'ν'45'out_40 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_40
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1126
-- Once.Denotation.TraceMonad.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_42 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_42 = erased
-- Once.Denotation.TraceMonad.M.eraseᵍ
d_erase'7501'_44 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_erase'7501'_44
  = coe MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92
-- Once.Denotation.TraceMonad.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_46 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_46 = erased
-- Once.Denotation.TraceMonad.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_48 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_48 = erased
-- Once.Denotation.TraceMonad.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_50 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_50 = erased
-- Once.Denotation.TraceMonad.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_52 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_52 = erased
-- Once.Denotation.TraceMonad.M.sem-CoIn
d_sem'45'CoIn_54 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_54
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1140
-- Once.Denotation.TraceMonad.M.sem-CoOut
d_sem'45'CoOut_56 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_56
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_1130
-- Once.Denotation.TraceMonad.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_58 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_58 = erased
-- Once.Denotation.TraceMonad.M.sem-In
d_sem'45'In_60 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_60
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_1060
-- Once.Denotation.TraceMonad.M.sem-In-Out
d_sem'45'In'45'Out_62 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_62 = erased
-- Once.Denotation.TraceMonad.M.sem-Out
d_sem'45'Out_64 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_64
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_1068
-- Once.Denotation.TraceMonad.M.sem-Out-In
d_sem'45'Out'45'In_66 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_66 = erased
-- Once.Denotation.TraceMonad.M.sem-ana
d_sem'45'ana_68 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_68 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1164 v0 v2 v3
-- Once.Denotation.TraceMonad.M.sem-case
d_sem'45'case_70 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_70 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_486 v3 v4 v5
-- Once.Denotation.TraceMonad.M.sem-case-inl
d_sem'45'case'45'inl_72 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_72 = erased
-- Once.Denotation.TraceMonad.M.sem-case-inr
d_sem'45'case'45'inr_74 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_74 = erased
-- Once.Denotation.TraceMonad.M.sem-cata
d_sem'45'cata_76 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_76 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_1080 v0 v1 v3
-- Once.Denotation.TraceMonad.M.sem-cata-compute
d_sem'45'cata'45'compute_78 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_78 = erased
-- Once.Denotation.TraceMonad.M.sem-fmap
d_sem'45'fmap_80 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_80 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_574 v0 v3 v4
-- Once.Denotation.TraceMonad.M.sem-fmap-Type
d_sem'45'fmap'45'Type_82 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_82 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_618 v0 v3
      v4
-- Once.Denotation.TraceMonad.M.sem-fst
d_sem'45'fst_84 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_84 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_450 v2
-- Once.Denotation.TraceMonad.M.sem-fst-pair
d_sem'45'fst'45'pair_86 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_86 = erased
-- Once.Denotation.TraceMonad.M.sem-functor-coherence
d_sem'45'functor'45'coherence_88 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_88 = erased
-- Once.Denotation.TraceMonad.M.sem-fuseNat
d_sem'45'fuseNat_90 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_90 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1314 v0 v1 v2
      v3 v5 v6
-- Once.Denotation.TraceMonad.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_92 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
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
-- Once.Denotation.TraceMonad.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_94 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_94 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1410
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Denotation.TraceMonad.M.sem-inl
d_sem'45'inl_96 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_96 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_472
-- Once.Denotation.TraceMonad.M.sem-inr
d_sem'45'inr_98 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_98 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_478
-- Once.Denotation.TraceMonad.M.sem-pair
d_sem'45'pair_100 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_100 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_462 v2 v3
-- Once.Denotation.TraceMonad.M.sem-para
d_sem'45'para_102 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_102 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_1096 v0 v1 v3 v4
-- Once.Denotation.TraceMonad.M.sem-snd
d_sem'45'snd_104 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_104 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_456 v2
-- Once.Denotation.TraceMonad.M.sem-snd-pair
d_sem'45'snd'45'pair_106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_106 = erased
-- Once.Denotation.TraceMonad.M.semAnaLayer
d_semAnaLayer_108 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_semAnaLayer_1170 v0 v2 v3
-- Once.Denotation.TraceMonad.M.sfmapSemAna
d_sfmapSemAna_110 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_110 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1178 v0 v1 v3 v4
-- Once.Denotation.TraceMonad.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_112 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_112 = erased
-- Once.Denotation.TraceMonad.M.⟦_⟧
d_'10214'_'10215'_114 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_114 = erased
-- Once.Denotation.TraceMonad.M.⟦_⟧F
d_'10214'_'10215'F_116 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_116 = erased
-- Once.Denotation.TraceMonad.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_118 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''7501'_118 = erased
-- Once.Denotation.TraceMonad.M.⟦μ⟧
d_'10214'μ'10215'_120 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'μ'10215'_120 = erased
-- Once.Denotation.TraceMonad.M.⟦ν⟧
d_'10214'ν'10215'_122 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'ν'10215'_122 = erased
-- Once.Denotation.TraceMonad.CallOp
d_CallOp_124 = ()
data T_CallOp_124
  = C_callOp_142 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
                 MAlonzo.Code.Once.Type.T_Type_108
-- Once.Denotation.TraceMonad.CallOp.cname
d_cname_134 ::
  T_CallOp_124 -> MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_cname_134 v0
  = case coe v0 of
      C_callOp_142 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.CallOp.cdom
d_cdom_136 :: T_CallOp_124 -> MAlonzo.Code.Once.Type.T_Type_108
d_cdom_136 v0
  = case coe v0 of
      C_callOp_142 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.CallOp.cbase
d_cbase_138 ::
  T_CallOp_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_cbase_138 v0
  = case coe v0 of
      C_callOp_142 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.CallOp.ccod
d_ccod_140 :: T_CallOp_124 -> MAlonzo.Code.Once.Type.T_Type_108
d_ccod_140 v0
  = case coe v0 of
      C_callOp_142 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.HaltOp
d_HaltOp_144 = ()
data T_HaltOp_144
  = C_haltOp_158 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
-- Once.Denotation.TraceMonad.HaltOp.hname
d_hname_152 ::
  T_HaltOp_144 -> MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_hname_152 v0
  = case coe v0 of
      C_haltOp_158 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.HaltOp.hdom
d_hdom_154 :: T_HaltOp_144 -> MAlonzo.Code.Once.Type.T_Type_108
d_hdom_154 v0
  = case coe v0 of
      C_haltOp_158 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.HaltOp.hbase
d_hbase_156 ::
  T_HaltOp_144 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_hbase_156 v0
  = case coe v0 of
      C_haltOp_158 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.callEvent
d_callEvent_162 ::
  T_CallOp_124 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124
d_callEvent_162 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Trace.C_mk'45'event_142
      (d_cname_134 (coe v0)) (d_cdom_136 (coe v0)) v1
-- Once.Denotation.TraceMonad.haltEvent
d_haltEvent_170 ::
  T_HaltOp_144 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124
d_haltEvent_170 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Trace.C_mk'45'event_142
      (d_hname_152 (coe v0)) (d_hdom_154 (coe v0)) v1
-- Once.Denotation.TraceMonad.T
d_T_178 a0 = ()
data T_T_178
  = C_ret_182 AgdaAny |
    C_call_186 T_CallOp_124 AgdaAny (AgdaAny -> T_T_178) |
    C_halt_190 T_HaltOp_144 AgdaAny
-- Once.Denotation.TraceMonad.returnT
d_returnT_194 :: () -> AgdaAny -> T_T_178
d_returnT_194 ~v0 = du_returnT_194
du_returnT_194 :: AgdaAny -> T_T_178
du_returnT_194 = coe C_ret_182
-- Once.Denotation.TraceMonad._>>=T_
d__'62''62''61'T__200 ::
  () -> () -> T_T_178 -> (AgdaAny -> T_T_178) -> T_T_178
d__'62''62''61'T__200 ~v0 ~v1 v2 v3 = du__'62''62''61'T__200 v2 v3
du__'62''62''61'T__200 ::
  T_T_178 -> (AgdaAny -> T_T_178) -> T_T_178
du__'62''62''61'T__200 v0 v1
  = case coe v0 of
      C_ret_182 v2 -> coe v1 v2
      C_call_186 v2 v3 v4
        -> coe
             C_call_186 (coe v2) (coe v3)
             (coe (\ v5 -> coe du__'62''62''61'T__200 (coe v4 v5) (coe v1)))
      C_halt_190 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad._>>T_
d__'62''62'T__226 :: () -> () -> T_T_178 -> T_T_178 -> T_T_178
d__'62''62'T__226 ~v0 ~v1 v2 v3 = du__'62''62'T__226 v2 v3
du__'62''62'T__226 :: T_T_178 -> T_T_178 -> T_T_178
du__'62''62'T__226 v0 v1
  = coe du__'62''62''61'T__200 (coe v0) (coe (\ v2 -> v1))
-- Once.Denotation.TraceMonad.fmapT
d_fmapT_238 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_T_178 -> T_T_178
d_fmapT_238 ~v0 ~v1 v2 v3 = du_fmapT_238 v2 v3
du_fmapT_238 :: (AgdaAny -> AgdaAny) -> T_T_178 -> T_T_178
du_fmapT_238 v0 v1
  = coe
      du__'62''62''61'T__200 (coe v1)
      (coe (\ v2 -> coe C_ret_182 (coe v0 v2)))
-- Once.Denotation.TraceMonad.callT
d_callT_248 :: T_CallOp_124 -> AgdaAny -> T_T_178
d_callT_248 v0 v1
  = coe C_call_186 (coe v0) (coe v1) (coe C_ret_182)
-- Once.Denotation.TraceMonad.haltT
d_haltT_258 :: () -> T_HaltOp_144 -> AgdaAny -> T_T_178
d_haltT_258 ~v0 v1 v2 = du_haltT_258 v1 v2
du_haltT_258 :: T_HaltOp_144 -> AgdaAny -> T_T_178
du_haltT_258 v0 v1 = coe C_halt_190 (coe v0) (coe v1)
-- Once.Denotation.TraceMonad.callKey
d_callKey_264 ::
  T_CallOp_124 -> MAlonzo.Code.Once.Spec.Contract.T_Key_124
d_callKey_264 v0
  = coe
      MAlonzo.Code.Once.Spec.Contract.C_key_138
      (coe
         MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
         (coe d_cname_134 (coe v0)))
      (coe d_cdom_136 (coe v0)) (coe d_ccod_140 (coe v0))
-- Once.Denotation.TraceMonad.Interp
d_Interp_268 = ()
data T_Interp_268
  = C_interp_278 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                 MAlonzo.Code.Once.Spec.Contract.T_Impl_292
-- Once.Denotation.TraceMonad.Interp.sig
d_sig_274 ::
  T_Interp_268 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sig_274 v0
  = case coe v0 of
      C_interp_278 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.Interp.impl
d_impl_276 ::
  T_Interp_268 -> MAlonzo.Code.Once.Spec.Contract.T_Impl_292
d_impl_276 v0
  = case coe v0 of
      C_interp_278 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.calls
d_calls_280 ::
  T_Interp_268 -> [MAlonzo.Code.Once.Spec.Contract.T_Key_124]
d_calls_280 v0
  = coe
      MAlonzo.Code.Once.Spec.Contract.d_answerKeys_276
      (coe d_sig_274 (coe v0))
-- Once.Denotation.TraceMonad.pures
d_pures_282 ::
  T_Interp_268 -> [MAlonzo.Code.Once.Spec.Contract.T_Key_124]
d_pures_282 v0
  = coe
      MAlonzo.Code.Once.Spec.Contract.d_valueKeys_274
      (coe d_sig_274 (coe v0))
-- Once.Denotation.TraceMonad.answer
d_answer_292 ::
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_CallOp_124 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_answer_292 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Contract.d_answerI_306 (d_impl_276 (coe v0))
      v1 (d_callKey_264 (coe v2)) v3
-- Once.Denotation.TraceMonad.pure
d_pure_306 ::
  T_Interp_268 ->
  MAlonzo.Code.Once.Spec.Contract.T_Key_124 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_pure_306 v0
  = coe
      MAlonzo.Code.Once.Spec.Contract.d_pureI_310
      (coe d_impl_276 (coe v0))
-- Once.Denotation.TraceMonad.no-world
d_no'45'world_310 :: T_Interp_268
d_no'45'world_310
  = coe
      C_interp_278 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.Spec.Contract.C_constructor_312 erased erased)
-- Once.Denotation.TraceMonad.unlinkedOp
d_unlinkedOp_318 :: T_HaltOp_144
d_unlinkedOp_318
  = coe
      C_haltOp_158
      (coe
         MAlonzo.Code.Once.CanonicalName.C_canonical_10
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe ("Generators" :: Data.Text.Text))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe ("unlinked" :: Data.Text.Text))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      (coe MAlonzo.Code.Once.Type.C_Unit_120)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
-- Once.Denotation.TraceMonad.unlinkedT
d_unlinkedT_322 :: () -> T_T_178
d_unlinkedT_322 ~v0 = du_unlinkedT_322
du_unlinkedT_322 :: T_T_178
du_unlinkedT_322
  = coe
      C_halt_190 (coe d_unlinkedOp_318)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Denotation.TraceMonad.resT
d_resT_326 :: () -> MAlonzo.Code.Once.Res.T_Res_6 -> T_T_178
d_resT_326 ~v0 v1 = du_resT_326 v1
du_resT_326 :: MAlonzo.Code.Once.Res.T_Res_6 -> T_T_178
du_resT_326 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe du_unlinkedT_322
      MAlonzo.Code.Once.Res.C_returns_12 v1 -> coe C_ret_182 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.pureHalf-at
d_pureHalf'45'at_334 ::
  T_Interp_268 ->
  MAlonzo.Code.Once.Spec.Contract.T_Key_124 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_pureHalf'45'at_334 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe
                           MAlonzo.Code.Once.Res.C_returns_12 (coe d_pure_306 v0 v1 v6 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v5) (coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.pureHalf
d_pureHalf_350 ::
  T_Interp_268 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_pureHalf_350 v0 v1 v2 v3
  = coe
      d_pureHalf'45'at_334 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Contract.C_key_138
         (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v1))
         (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.Spec.Contract.d__'8712'K'63'__176
         (coe
            MAlonzo.Code.Once.Spec.Contract.C_key_138
            (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v1))
            (coe v2) (coe v3))
         (d_pures_282 (coe v0)))
-- Once.Denotation.TraceMonad.Run
d_Run_360 :: () -> ()
d_Run_360 = erased
-- Once.Denotation.TraceMonad.consE
d_consE_366 ::
  () ->
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_consE_366 ~v0 v1 v2 = du_consE_366 v1 v2
du_consE_366 ::
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_consE_366 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
-- Once.Denotation.TraceMonad.appE
d_appE_374 ::
  () ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appE_374 ~v0 v1 v2 = du_appE_374 v1 v2
du_appE_374 ::
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_appE_374 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
-- Once.Denotation.TraceMonad.callAnswer-at
d_callAnswer'45'at_384 ::
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_CallOp_124 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe AgdaAny
d_callAnswer'45'at_384 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             else coe
                    seq (coe v7)
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then case coe v9 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe d_answer_292 v0 v1 v2 v10 v3)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v9) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.callAnswer
d_callAnswer_418 ::
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_CallOp_124 -> AgdaAny -> Maybe AgdaAny
d_callAnswer_418 v0 v1 v2 v3
  = coe
      d_callAnswer'45'at_384 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Type.d_isUnit'63'_168 (coe d_ccod_140 (coe v2)))
      (coe
         MAlonzo.Code.Once.Spec.Contract.d__'8712'K'63'__176
         (d_callKey_264 (coe v2)) (d_calls_280 (coe v0)))
-- Once.Denotation.TraceMonad.run
d_run_430 ::
  () ->
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_T_178 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run_430 ~v0 v1 v2 v3 = du_run_430 v1 v2 v3
du_run_430 ::
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_T_178 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run_430 v0 v1 v2
  = case coe v2 of
      C_ret_182 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Once.Res.C_returns_12 (coe v3))
      C_call_186 v3 v4 v5
        -> coe
             du_run'45'call_438 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             (coe d_callAnswer_418 (coe v0) (coe v1) (coe v3) (coe v4))
      C_halt_190 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe d_haltEvent_170 (coe v3) (coe v4)))
             (coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.run-call
d_run'45'call_438 ::
  () ->
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_CallOp_124 ->
  AgdaAny ->
  (AgdaAny -> T_T_178) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'call_438 ~v0 v1 v2 v3 v4 v5 v6
  = du_run'45'call_438 v1 v2 v3 v4 v5 v6
du_run'45'call_438 ::
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_CallOp_124 ->
  AgdaAny ->
  (AgdaAny -> T_T_178) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'call_438 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_consE_366 (coe d_callEvent_162 (coe v2) (coe v3))
             (coe
                du_run_430 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe d_callEvent_162 (coe v2) (coe v3))))
                (coe v4 v6))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   d_haltEvent_170 (coe d_unlinkedOp_318)
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             (coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.thenRes
d_thenRes_490 ::
  () ->
  () ->
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_178) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thenRes_490 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_thenRes_490 v2 v3 v4 v5 v6
du_thenRes_490 ::
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_178) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thenRes_490 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      MAlonzo.Code.Once.Res.C_returns_12 v5
        -> coe
             du_appE_374 (coe v2)
             (coe
                du_run_430 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
                (coe v4 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.then
d_then_514 ::
  () ->
  () ->
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> T_T_178) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_then_514 ~v0 ~v1 v2 v3 v4 v5 = du_then_514 v2 v3 v4 v5
du_then_514 ::
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> T_T_178) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_then_514 v0 v1 v2 v3
  = coe
      du_thenRes_490 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)) (coe v3)
-- Once.Denotation.TraceMonad.eventsT
d_eventsT_526 ::
  () ->
  T_Interp_268 ->
  T_T_178 -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_eventsT_526 ~v0 v1 v2 = du_eventsT_526 v1 v2
du_eventsT_526 ::
  T_Interp_268 ->
  T_T_178 -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_eventsT_526 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_run_430 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1))
-- Once.Denotation.TraceMonad.resultT
d_resultT_534 ::
  () -> T_Interp_268 -> T_T_178 -> MAlonzo.Code.Once.Res.T_Res_6
d_resultT_534 ~v0 v1 v2 = du_resultT_534 v1 v2
du_resultT_534 ::
  T_Interp_268 -> T_T_178 -> MAlonzo.Code.Once.Res.T_Res_6
du_resultT_534 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_run_430 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1))
-- Once.Denotation.TraceMonad.projTrace
d_projTrace_542 ::
  () ->
  T_Interp_268 ->
  T_T_178 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_projTrace_542 ~v0 v1 v2 v3 = du_projTrace_542 v1 v2 v3
du_projTrace_542 ::
  T_Interp_268 ->
  T_T_178 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_projTrace_542 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530 (coe v2)
      (coe du_eventsT_526 (coe v0) (coe v1))
-- Once.Denotation.TraceMonad.atT
d_atT_552 ::
  () ->
  T_Interp_268 ->
  T_T_178 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atT_552 ~v0 v1 v2 v3 = du_atT_552 v1 v2 v3
du_atT_552 ::
  T_Interp_268 ->
  T_T_178 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_atT_552 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_projTrace_542 (coe v0) (coe v1) (coe v2))
      (coe du_resultT_534 (coe v0) (coe v1))
-- Once.Denotation.TraceMonad.Stopped
d_Stopped_560 :: ()
d_Stopped_560 = erased
-- Once.Denotation.TraceMonad.stoppedT
d_stoppedT_564 :: () -> T_Interp_268 -> T_T_178 -> Bool
d_stoppedT_564 ~v0 v1 v2 = du_stoppedT_564 v1 v2
du_stoppedT_564 :: T_Interp_268 -> T_T_178 -> Bool
du_stoppedT_564 v0 v1
  = coe
      MAlonzo.Code.Once.Res.du_is'45'stopped_16
      (coe du_resultT_534 (coe v0) (coe v1))
-- Once.Denotation.TraceMonad.Bounded
d_Bounded_570 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  ()
d_Bounded_570 = erased
-- Once.Denotation.TraceMonad.Saturating
d_Saturating_576 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  ()
d_Saturating_576 = erased
-- Once.Denotation.TraceMonad.Coherent
d_Coherent_582 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  ()
d_Coherent_582 = erased
-- Once.Denotation.TraceMonad.PrefixFamily
d_PrefixFamily_592 a0 = ()
data T_PrefixFamily_592
  = C_prefixFamily_608 (Integer ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Denotation.TraceMonad.PrefixFamily.bnd
d_bnd_602 ::
  T_PrefixFamily_592 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_602 v0
  = case coe v0 of
      C_prefixFamily_608 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.PrefixFamily.sat
d_sat_604 ::
  T_PrefixFamily_592 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat_604 = erased
-- Once.Denotation.TraceMonad.PrefixFamily.coh
d_coh_606 ::
  T_PrefixFamily_592 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coh_606 v0
  = case coe v0 of
      C_prefixFamily_608 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.Returns?
d_Returns'63'_612 :: () -> MAlonzo.Code.Once.Res.T_Res_6 -> ()
d_Returns'63'_612 = erased
-- Once.Denotation.TraceMonad.resVal
d_resVal_618 ::
  () -> MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny -> AgdaAny
d_resVal_618 ~v0 v1 ~v2 = du_resVal_618 v1
du_resVal_618 :: MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
du_resVal_618 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_returns_12 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.resultAt
d_resultAt_624 ::
  () ->
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_T_178 -> MAlonzo.Code.Once.Res.T_Res_6
d_resultAt_624 ~v0 v1 v2 v3 = du_resultAt_624 v1 v2 v3
du_resultAt_624 ::
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_T_178 -> MAlonzo.Code.Once.Res.T_Res_6
du_resultAt_624 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe du_run_430 (coe v0) (coe v1) (coe v2))
-- Once.Denotation.TraceMonad.valueT
d_valueT_642 ::
  () ->
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_T_178 -> AgdaAny -> AgdaAny
d_valueT_642 ~v0 v1 v2 v3 ~v4 = du_valueT_642 v1 v2 v3
du_valueT_642 ::
  T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_T_178 -> AgdaAny
du_valueT_642 v0 v1 v2
  = coe
      du_resVal_618 (coe du_resultAt_624 (coe v0) (coe v1) (coe v2))
-- Once.Denotation.TraceMonad.RelRes
d_RelRes_658 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> ()
d_RelRes_658 = erased
-- Once.Denotation.TraceMonad.RelT′
d_RelT'8242'_666 a0 a1 a2 a3 a4 = ()
data T_RelT'8242'_666
  = C_rel'45'ret_678 AgdaAny |
    C_rel'45'call_690 (AgdaAny -> T_RelT'8242'_666) | C_rel'45'halt_696
