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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.SigOp.Info.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_650
-- Once.SigOp.Info.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_10 = erased
-- Once.SigOp.Info.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 = erased
-- Once.SigOp.Info.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_14 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_14
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_614
-- Once.SigOp.Info.M.coerce-functor
d_coerce'45'functor_16 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_110 v0 v2
-- Once.SigOp.Info.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_18 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_152
      v0 v2
-- Once.SigOp.Info.M.coerce-round-trip
d_coerce'45'round'45'trip_20 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_20 = erased
-- Once.SigOp.Info.M.coerce-struct
d_coerce'45'struct_22 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_22
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_282
-- Once.SigOp.Info.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_24 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_24 = erased
-- Once.SigOp.Info.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_26 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_26
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_288
-- Once.SigOp.Info.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_28 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_28 = erased
-- Once.SigOp.Info.M.coerce-μ-in
d_coerce'45'μ'45'in_30 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_30 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_762 v0 v2
-- Once.SigOp.Info.M.coerce-μ-out
d_coerce'45'μ'45'out_32 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_32 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804 v0 v1
      v3
-- Once.SigOp.Info.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_34 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_34 = erased
-- Once.SigOp.Info.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_36 = erased
-- Once.SigOp.Info.M.coerce-ν-in
d_coerce'45'ν'45'in_38 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_38
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_996
-- Once.SigOp.Info.M.coerce-ν-out
d_coerce'45'ν'45'out_40 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_40
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1002
-- Once.SigOp.Info.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_42 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_42 = erased
-- Once.SigOp.Info.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_44 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_44 = erased
-- Once.SigOp.Info.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_46 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_46 = erased
-- Once.SigOp.Info.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_48 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_48 = erased
-- Once.SigOp.Info.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_50 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_50 = erased
-- Once.SigOp.Info.M.sem-CoIn
d_sem'45'CoIn_52 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_52
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1016
-- Once.SigOp.Info.M.sem-CoOut
d_sem'45'CoOut_54 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_54
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_1006
-- Once.SigOp.Info.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_56 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_56 = erased
-- Once.SigOp.Info.M.sem-In
d_sem'45'In_58 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_58
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_936
-- Once.SigOp.Info.M.sem-In-Out
d_sem'45'In'45'Out_60 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_60 = erased
-- Once.SigOp.Info.M.sem-Out
d_sem'45'Out_62 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_62
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_944
-- Once.SigOp.Info.M.sem-Out-In
d_sem'45'Out'45'In_64 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_64 = erased
-- Once.SigOp.Info.M.sem-ana
d_sem'45'ana_66 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_66 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1040 v0 v2 v3
-- Once.SigOp.Info.M.sem-case
d_sem'45'case_68 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_68 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_346 v3 v4 v5
-- Once.SigOp.Info.M.sem-case-inl
d_sem'45'case'45'inl_70 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_70 = erased
-- Once.SigOp.Info.M.sem-case-inr
d_sem'45'case'45'inr_72 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_72 = erased
-- Once.SigOp.Info.M.sem-cata
d_sem'45'cata_74 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_74 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_956 v0 v1 v3
-- Once.SigOp.Info.M.sem-cata-compute
d_sem'45'cata'45'compute_76 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_76 = erased
-- Once.SigOp.Info.M.sem-fmap
d_sem'45'fmap_78 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_78 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_434 v0 v3 v4
-- Once.SigOp.Info.M.sem-fmap-Type
d_sem'45'fmap'45'Type_80 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_80 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_478 v0 v3
      v4
-- Once.SigOp.Info.M.sem-fst
d_sem'45'fst_82 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_82 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_310 v2
-- Once.SigOp.Info.M.sem-fst-pair
d_sem'45'fst'45'pair_84 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_84 = erased
-- Once.SigOp.Info.M.sem-functor-coherence
d_sem'45'functor'45'coherence_86 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_86 = erased
-- Once.SigOp.Info.M.sem-fuseNat
d_sem'45'fuseNat_88 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_88 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat_1190 v0 v1 v2
      v3 v5 v6
-- Once.SigOp.Info.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_90 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
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
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_92 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1286
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.SigOp.Info.M.sem-inl
d_sem'45'inl_94 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_94 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_332
-- Once.SigOp.Info.M.sem-inr
d_sem'45'inr_96 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_96 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_338
-- Once.SigOp.Info.M.sem-pair
d_sem'45'pair_98 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_98 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_322 v2 v3
-- Once.SigOp.Info.M.sem-para
d_sem'45'para_100 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_100 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_972 v0 v1 v3 v4
-- Once.SigOp.Info.M.sem-snd
d_sem'45'snd_102 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_102 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_316 v2
-- Once.SigOp.Info.M.sem-snd-pair
d_sem'45'snd'45'pair_104 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_104 = erased
-- Once.SigOp.Info.M.semAnaLayer
d_semAnaLayer_106 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_106 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_semAnaLayer_1046 v0 v2 v3
-- Once.SigOp.Info.M.sfmapSemAna
d_sfmapSemAna_108 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_108 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1054 v0 v1 v3 v4
-- Once.SigOp.Info.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_110 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_110 = erased
-- Once.SigOp.Info.M.⟦_⟧
d_'10214'_'10215'_112 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_112 = erased
-- Once.SigOp.Info.M.⟦_⟧F
d_'10214'_'10215'F_114 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_114 = erased
-- Once.SigOp.Info.M.⟦μ⟧
d_'10214'μ'10215'_116 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'μ'10215'_116 = erased
-- Once.SigOp.Info.M.⟦ν⟧
d_'10214'ν'10215'_118 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'ν'10215'_118 = erased
-- Once.SigOp.Info.EffectShape
d_EffectShape_122 a0 = ()
data T_EffectShape_122 = C_Pure_126 | C_Emits_128 | C_Halts_130
-- Once.SigOp.Info.SigOpSem
d_SigOpSem_136 a0 a1 = ()
data T_SigOpSem_136
  = C_pureV_142 (MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
                 AgdaAny -> AgdaAny) |
    C_emitsV_144 | C_haltsV_146
-- Once.SigOp.Info.Linkage
d_Linkage_150 a0 = ()
data T_Linkage_150
  = C_ffi'45'concrete_154 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_internal'45'ref_156
-- Once.SigOp.Info.SigOpInfo
d_SigOpInfo_162 a0 a1 = ()
data T_SigOpInfo_162
  = C_mk'45'info''_184 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                       T_SigOpSem_136 MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
                       T_Linkage_150
-- Once.SigOp.Info.SigOpInfo.name
d_name_176 ::
  T_SigOpInfo_162 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_name_176 v0
  = case coe v0 of
      C_mk'45'info''_184 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.sem
d_sem_178 :: T_SigOpInfo_162 -> T_SigOpSem_136
d_sem_178 v0
  = case coe v0 of
      C_mk'45'info''_184 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.baseA
d_baseA_180 ::
  T_SigOpInfo_162 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_baseA_180 v0
  = case coe v0 of
      C_mk'45'info''_184 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.conB
d_conB_182 :: T_SigOpInfo_162 -> T_Linkage_150
d_conB_182 v0
  = case coe v0 of
      C_mk'45'info''_184 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.semM-of
d_semM'45'of_190 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_SigOpSem_136 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_semM'45'of_190 ~v0 ~v1 v2 = du_semM'45'of_190 v2
du_semM'45'of_190 ::
  T_SigOpSem_136 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
du_semM'45'of_190 v0
  = case coe v0 of
      C_pureV_142 v1
        -> coe
             (\ v2 v3 -> coe MAlonzo.Code.Once.Res.C_returns_12 (coe v1 v2 v3))
      C_emitsV_144
        -> coe
             (\ v2 v3 ->
                coe
                  MAlonzo.Code.Once.Res.C_returns_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      C_haltsV_146
        -> coe (\ v2 v3 -> coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.effect-of
d_effect'45'of_210 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_SigOpSem_136 -> T_EffectShape_122
d_effect'45'of_210 ~v0 ~v1 v2 = du_effect'45'of_210 v2
du_effect'45'of_210 :: T_SigOpSem_136 -> T_EffectShape_122
du_effect'45'of_210 v0
  = case coe v0 of
      C_pureV_142 v1 -> coe C_Pure_126
      C_emitsV_144 -> coe C_Emits_128
      C_haltsV_146 -> coe C_Halts_130
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.semM
d_semM_220 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_SigOpInfo_162 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_semM_220 ~v0 ~v1 v2 = du_semM_220 v2
du_semM_220 ::
  T_SigOpInfo_162 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
du_semM_220 v0 = coe du_semM'45'of_190 (coe d_sem_178 (coe v0))
-- Once.SigOp.Info.effect
d_effect_228 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_SigOpInfo_162 -> T_EffectShape_122
d_effect_228 ~v0 ~v1 v2 = du_effect_228 v2
du_effect_228 :: T_SigOpInfo_162 -> T_EffectShape_122
du_effect_228 v0 = coe du_effect'45'of_210 (coe d_sem_178 (coe v0))
-- Once.SigOp.Info.stops-shape
d_stops'45'shape_234 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_EffectShape_122 -> Bool
d_stops'45'shape_234 ~v0 v1 = du_stops'45'shape_234 v1
du_stops'45'shape_234 :: T_EffectShape_122 -> Bool
du_stops'45'shape_234 v0
  = case coe v0 of
      C_Pure_126 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_Emits_128 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_Halts_130 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.semM-stops-of
d_semM'45'stops'45'of_246 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_SigOpSem_136 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semM'45'stops'45'of_246 = erased
-- Once.SigOp.Info.semM-stops
d_semM'45'stops_272 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_SigOpInfo_162 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semM'45'stops_272 = erased
-- Once.SigOp.Info.mk-info
d_mk'45'info_280 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
   AgdaAny -> AgdaAny) ->
  T_EffectShape_122 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  T_SigOpInfo_162
d_mk'45'info_280 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_mk'45'info_280 v2 v3 v4 v5 v6
du_mk'45'info_280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  (MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
   AgdaAny -> AgdaAny) ->
  T_EffectShape_122 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  T_SigOpInfo_162
du_mk'45'info_280 v0 v1 v2 v3 v4
  = case coe v2 of
      C_Pure_126
        -> coe
             C_mk'45'info''_184 (coe v0) (coe C_pureV_142 (coe v1)) (coe v3)
             (coe C_ffi'45'concrete_154 (coe v4))
      C_Emits_128
        -> coe
             C_mk'45'info''_184 (coe v0) (coe C_emitsV_144) (coe v3)
             (coe C_ffi'45'concrete_154 (coe v4))
      C_Halts_130
        -> coe
             C_mk'45'info''_184 (coe v0) (coe C_haltsV_146) (coe v3)
             (coe C_ffi'45'concrete_154 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info._≟SigOpInfo-name_
d__'8799'SigOpInfo'45'name__318 ::
  T_SigOpInfo_162 ->
  T_SigOpInfo_162 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'SigOpInfo'45'name__318 v0 v1
  = coe
      MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__110
      (coe d_name_176 (coe v0)) (coe d_name_176 (coe v1))
-- Once.SigOp.Info.sigOpInfo-name-coherence
d_sigOpInfo'45'name'45'coherence_332
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SigOp.Info.sigOpInfo-name-coherence"
-- Once.SigOp.Info._≟SigOpInfo_
d__'8799'SigOpInfo__342 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_SigOpInfo_162 ->
  T_SigOpInfo_162 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'SigOpInfo__342 ~v0 ~v1 v2 v3
  = du__'8799'SigOpInfo__342 v2 v3
du__'8799'SigOpInfo__342 ::
  T_SigOpInfo_162 ->
  T_SigOpInfo_162 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'SigOpInfo__342 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
              (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54)
              (coe
                 MAlonzo.Code.Once.CanonicalName.d_parts_8
                 (coe d_name_176 (coe v0)))
              (coe
                 MAlonzo.Code.Once.CanonicalName.d_parts_8
                 (coe d_name_176 (coe v1))) in
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
