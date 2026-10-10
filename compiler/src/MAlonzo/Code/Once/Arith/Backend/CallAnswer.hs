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

module MAlonzo.Code.Once.Arith.Backend.CallAnswer where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Arith.Backend.CallAnswer.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_10
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_786
-- Once.Arith.Backend.CallAnswer.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_12 = erased
-- Once.Arith.Backend.CallAnswer.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_14 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_14 = erased
-- Once.Arith.Backend.CallAnswer.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_16 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_16
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_754
-- Once.Arith.Backend.CallAnswer.M.coerce-functor
d_coerce'45'functor_18 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_250 v0 v2
-- Once.Arith.Backend.CallAnswer.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_20 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_20 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_292
      v0 v2
-- Once.Arith.Backend.CallAnswer.M.coerce-round-trip
d_coerce'45'round'45'trip_22 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_22 = erased
-- Once.Arith.Backend.CallAnswer.M.coerce-struct
d_coerce'45'struct_24 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_24
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_422
-- Once.Arith.Backend.CallAnswer.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_26 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_26 = erased
-- Once.Arith.Backend.CallAnswer.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_28 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_28
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_428
-- Once.Arith.Backend.CallAnswer.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_30 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_30 = erased
-- Once.Arith.Backend.CallAnswer.M.coerce-μ-in
d_coerce'45'μ'45'in_32 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_32 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_886 v0 v2
-- Once.Arith.Backend.CallAnswer.M.coerce-μ-out
d_coerce'45'μ'45'out_34 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_34 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928 v0 v1
      v3
-- Once.Arith.Backend.CallAnswer.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_36 = erased
-- Once.Arith.Backend.CallAnswer.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_38 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_38 = erased
-- Once.Arith.Backend.CallAnswer.M.coerce-ν-in
d_coerce'45'ν'45'in_40 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_40
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120
-- Once.Arith.Backend.CallAnswer.M.coerce-ν-out
d_coerce'45'ν'45'out_42 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_42
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1126
-- Once.Arith.Backend.CallAnswer.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_44 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_44 = erased
-- Once.Arith.Backend.CallAnswer.M.eraseᵍ
d_erase'7501'_46 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_erase'7501'_46
  = coe MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92
-- Once.Arith.Backend.CallAnswer.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_48 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_48 = erased
-- Once.Arith.Backend.CallAnswer.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_50 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_50 = erased
-- Once.Arith.Backend.CallAnswer.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_52 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_52 = erased
-- Once.Arith.Backend.CallAnswer.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_54 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_54 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-CoIn
d_sem'45'CoIn_56 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_56
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1140
-- Once.Arith.Backend.CallAnswer.M.sem-CoOut
d_sem'45'CoOut_58 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_58
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_1130
-- Once.Arith.Backend.CallAnswer.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_60 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_60 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-In
d_sem'45'In_62 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_62
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_1060
-- Once.Arith.Backend.CallAnswer.M.sem-In-Out
d_sem'45'In'45'Out_64 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_64 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-Out
d_sem'45'Out_66 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_66
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_1068
-- Once.Arith.Backend.CallAnswer.M.sem-Out-In
d_sem'45'Out'45'In_68 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_68 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-ana
d_sem'45'ana_70 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_70 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1164 v0 v2 v3
-- Once.Arith.Backend.CallAnswer.M.sem-case
d_sem'45'case_72 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_72 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_486 v3 v4 v5
-- Once.Arith.Backend.CallAnswer.M.sem-case-inl
d_sem'45'case'45'inl_74 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_74 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-case-inr
d_sem'45'case'45'inr_76 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_76 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-cata
d_sem'45'cata_78 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_78 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_1080 v0 v1 v3
-- Once.Arith.Backend.CallAnswer.M.sem-cata-compute
d_sem'45'cata'45'compute_80 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_80 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-fmap
d_sem'45'fmap_82 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_82 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_574 v0 v3 v4
-- Once.Arith.Backend.CallAnswer.M.sem-fmap-Type
d_sem'45'fmap'45'Type_84 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_84 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_618 v0 v3
      v4
-- Once.Arith.Backend.CallAnswer.M.sem-fst
d_sem'45'fst_86 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_86 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_450 v2
-- Once.Arith.Backend.CallAnswer.M.sem-fst-pair
d_sem'45'fst'45'pair_88 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_88 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-functor-coherence
d_sem'45'functor'45'coherence_90 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_90 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-fuseNat
d_sem'45'fuseNat_92 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_92 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1314 v0 v1 v2
      v3 v5 v6
-- Once.Arith.Backend.CallAnswer.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_94 ::
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
d_sem'45'fuseNat'45'cong_94 = erased
-- Once.Arith.Backend.CallAnswer.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_96 ::
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
d_sem'45'fuseNat'45'events_96 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1410
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.Backend.CallAnswer.M.sem-inl
d_sem'45'inl_98 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_98 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_472
-- Once.Arith.Backend.CallAnswer.M.sem-inr
d_sem'45'inr_100 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_100 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_478
-- Once.Arith.Backend.CallAnswer.M.sem-pair
d_sem'45'pair_102 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_102 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_462 v2 v3
-- Once.Arith.Backend.CallAnswer.M.sem-para
d_sem'45'para_104 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_104 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_1096 v0 v1 v3 v4
-- Once.Arith.Backend.CallAnswer.M.sem-snd
d_sem'45'snd_106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_106 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_456 v2
-- Once.Arith.Backend.CallAnswer.M.sem-snd-pair
d_sem'45'snd'45'pair_108 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_108 = erased
-- Once.Arith.Backend.CallAnswer.M.semAnaLayer
d_semAnaLayer_110 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_110 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_semAnaLayer_1170 v0 v2 v3
-- Once.Arith.Backend.CallAnswer.M.sfmapSemAna
d_sfmapSemAna_112 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_112 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1178 v0 v1 v3 v4
-- Once.Arith.Backend.CallAnswer.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_114 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_114 = erased
-- Once.Arith.Backend.CallAnswer.M.⟦_⟧
d_'10214'_'10215'_116 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_116 = erased
-- Once.Arith.Backend.CallAnswer.M.⟦_⟧F
d_'10214'_'10215'F_118 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_118 = erased
-- Once.Arith.Backend.CallAnswer.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_120 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''7501'_120 = erased
-- Once.Arith.Backend.CallAnswer.M.⟦μ⟧
d_'10214'μ'10215'_122 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'μ'10215'_122 = erased
-- Once.Arith.Backend.CallAnswer.M.⟦ν⟧
d_'10214'ν'10215'_124 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'ν'10215'_124 = erased
-- Once.Arith.Backend.CallAnswer.answer-word
d_answer'45'word_128 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> Integer
d_answer'45'word_128 v0 v1
  = let v2 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Int_134 -> coe v1
         MAlonzo.Code.Once.Type.C_Float_136 -> coe v1
         _ -> coe v2)
-- Once.Arith.Backend.CallAnswer.ResolvedCall
d_ResolvedCall_134 = ()
data T_ResolvedCall_134
  = C_answering_138 MAlonzo.Code.Once.Denotation.TraceMonad.T_CallOp_124
                    AgdaAny |
    C_pure'45'ffi_146 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                      MAlonzo.Code.Once.Type.T_Type_108 MAlonzo.Code.Once.Type.T_Type_108
                      AgdaAny
-- Once.Arith.Backend.CallAnswer.CallResolver
d_CallResolver_148 :: () -> ()
d_CallResolver_148 = erased
-- Once.Arith.Backend.CallAnswer.answering-word
d_answering'45'word_156 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_CallOp_124 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_answering'45'word_156 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then case coe v6 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                      -> coe
                           d_answer'45'word_128
                           (coe MAlonzo.Code.Once.Denotation.TraceMonad.d_ccod_140 (coe v2))
                           (coe
                              MAlonzo.Code.Once.Denotation.TraceMonad.d_answer_292 v0 v1 v2 v7
                              v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v6) (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.CallAnswer.value-word
d_value'45'word_180 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268 ->
  MAlonzo.Code.Once.Spec.Contract.T_Key_124 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_value'45'word_180 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe
                           d_answer'45'word_128
                           (coe MAlonzo.Code.Once.Spec.Contract.d_kcod_136 (coe v1))
                           (coe
                              MAlonzo.Code.Once.Denotation.TraceMonad.d_pure_306 v0 v1 v6 v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v5) (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.CallAnswer.resolved-word
d_resolved'45'word_196 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  T_ResolvedCall_134 -> Integer
d_resolved'45'word_196 v0 v1 v2
  = case coe v2 of
      C_answering_138 v3 v4
        -> coe
             d_answering'45'word_156 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.Spec.Contract.d__'8712'K'63'__176
                (MAlonzo.Code.Once.Denotation.TraceMonad.d_callKey_264 (coe v3))
                (MAlonzo.Code.Once.Denotation.TraceMonad.d_calls_280 (coe v0)))
      C_pure'45'ffi_146 v3 v4 v5 v6
        -> coe
             d_value'45'word_180 (coe v0)
             (coe
                MAlonzo.Code.Once.Spec.Contract.C_key_138
                (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v3))
                (coe v4) (coe v5))
             (coe v6)
             (coe
                MAlonzo.Code.Once.Spec.Contract.d__'8712'K'63'__176
                (coe
                   MAlonzo.Code.Once.Spec.Contract.C_key_138
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v3))
                   (coe v4) (coe v5))
                (MAlonzo.Code.Once.Denotation.TraceMonad.d_pures_282 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.CallAnswer.answer-at
d_answer'45'at_220 ::
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> Maybe T_ResolvedCall_134) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> Integer
d_answer'45'at_220 ~v0 v1 v2 v3 v4 v5
  = du_answer'45'at_220 v1 v2 v3 v4 v5
du_answer'45'at_220 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> Maybe T_ResolvedCall_134) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> Integer
du_answer'45'at_220 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44
      (d_resolved'45'word_196 (coe v0) (coe v2)) (0 :: Integer)
      (coe v1 v3 v4)
