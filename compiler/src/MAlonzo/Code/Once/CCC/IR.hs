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

module MAlonzo.Code.Once.CCC.IR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.IR.I.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_634
-- Once.CCC.IR.I.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_10 = erased
-- Once.CCC.IR.I.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 = erased
-- Once.CCC.IR.I.coerce-full-to-base
d_coerce'45'full'45'to'45'base_14 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_14
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_598
-- Once.CCC.IR.I.coerce-functor
d_coerce'45'functor_16 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_94 v0 v2
-- Once.CCC.IR.I.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_136
      v0 v2
-- Once.CCC.IR.I.coerce-round-trip
d_coerce'45'round'45'trip_20 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_20 = erased
-- Once.CCC.IR.I.coerce-struct
d_coerce'45'struct_22 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_22
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_266
-- Once.CCC.IR.I.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_24 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_24 = erased
-- Once.CCC.IR.I.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_26 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_26
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_272
-- Once.CCC.IR.I.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_28 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_28 = erased
-- Once.CCC.IR.I.coerce-μ-in
d_coerce'45'μ'45'in_30 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_30 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_746 v0 v2
-- Once.CCC.IR.I.coerce-μ-out
d_coerce'45'μ'45'out_32 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_32 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_788 v0 v1 v3
-- Once.CCC.IR.I.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_34 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_34 = erased
-- Once.CCC.IR.I.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_36 = erased
-- Once.CCC.IR.I.coerce-ν-in
d_coerce'45'ν'45'in_38 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_38
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_980
-- Once.CCC.IR.I.coerce-ν-out
d_coerce'45'ν'45'out_40 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_40
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_986
-- Once.CCC.IR.I.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_42 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_42 = erased
-- Once.CCC.IR.I.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_44 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_44 = erased
-- Once.CCC.IR.I.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_46 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_46 = erased
-- Once.CCC.IR.I.fmap-struct-coherence
d_fmap'45'struct'45'coherence_48 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_48 = erased
-- Once.CCC.IR.I.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_50 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_50 = erased
-- Once.CCC.IR.I.sem-CoIn
d_sem'45'CoIn_52 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_198
d_sem'45'CoIn_52
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1000
-- Once.CCC.IR.I.sem-CoOut
d_sem'45'CoOut_54 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 -> AgdaAny
d_sem'45'CoOut_54
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_990
-- Once.CCC.IR.I.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_56 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_56 = erased
-- Once.CCC.IR.I.sem-In
d_sem'45'In_58 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_182
d_sem'45'In_58
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_920
-- Once.CCC.IR.I.sem-In-Out
d_sem'45'In'45'Out_60 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_60 = erased
-- Once.CCC.IR.I.sem-Out
d_sem'45'Out_62 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'Out_62
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_928
-- Once.CCC.IR.I.sem-Out-In
d_sem'45'Out'45'In_64 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_64 = erased
-- Once.CCC.IR.I.sem-ana
d_sem'45'ana_66 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_198
d_sem'45'ana_66 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1024 v0 v2 v3
-- Once.CCC.IR.I.sem-case
d_sem'45'case_68 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_68 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_330 v3 v4 v5
-- Once.CCC.IR.I.sem-case-inl
d_sem'45'case'45'inl_70 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_70 = erased
-- Once.CCC.IR.I.sem-case-inr
d_sem'45'case'45'inr_72 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_72 = erased
-- Once.CCC.IR.I.sem-cata
d_sem'45'cata_74 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'cata_74 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_940 v0 v1 v3
-- Once.CCC.IR.I.sem-cata-compute
d_sem'45'cata'45'compute_76 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_76 = erased
-- Once.CCC.IR.I.sem-fmap
d_sem'45'fmap_78 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_78 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_418 v0 v3 v4
-- Once.CCC.IR.I.sem-fmap-Type
d_sem'45'fmap'45'Type_80 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_80 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_462 v0 v3
      v4
-- Once.CCC.IR.I.sem-fst
d_sem'45'fst_82 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_82 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_294 v2
-- Once.CCC.IR.I.sem-fst-pair
d_sem'45'fst'45'pair_84 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_84 = erased
-- Once.CCC.IR.I.sem-functor-coherence
d_sem'45'functor'45'coherence_86 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_86 = erased
-- Once.CCC.IR.I.sem-fuseNat
d_sem'45'fuseNat_88 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_88 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1154 v0 v1 v2 v3
      v5 v6
-- Once.CCC.IR.I.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_90 ::
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
d_sem'45'fuseNat'45'cong_90 = erased
-- Once.CCC.IR.I.sem-fuseNat-events
d_sem'45'fuseNat'45'events_92 ::
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
d_sem'45'fuseNat'45'events_92 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat'45'events_1250
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.CCC.IR.I.sem-inl
d_sem'45'inl_94 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_94 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_316
-- Once.CCC.IR.I.sem-inr
d_sem'45'inr_96 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_96 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_322
-- Once.CCC.IR.I.sem-pair
d_sem'45'pair_98 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_98 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_306 v2 v3
-- Once.CCC.IR.I.sem-para
d_sem'45'para_100 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'para_100 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_956 v0 v1 v3 v4
-- Once.CCC.IR.I.sem-snd
d_sem'45'snd_102 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_102 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_300 v2
-- Once.CCC.IR.I.sem-snd-pair
d_sem'45'snd'45'pair_104 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_104 = erased
-- Once.CCC.IR.I.sfmapSemAna
d_sfmapSemAna_106 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_106 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmapSemAna_1032 v0 v1 v3 v4
-- Once.CCC.IR.I.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_108 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_108 = erased
-- Once.CCC.IR.I.⟦_⟧
d_'10214'_'10215'_110 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_110 = erased
-- Once.CCC.IR.I.⟦_⟧F
d_'10214'_'10215'F_112 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_112 = erased
-- Once.CCC.IR.I.⟦μ⟧
d_'10214'μ'10215'_114 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_114 = erased
-- Once.CCC.IR.I.⟦ν⟧
d_'10214'ν'10215'_116 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_116 = erased
-- Once.CCC.IR.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_120 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_120
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_634
-- Once.CCC.IR.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_122 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_122 = erased
-- Once.CCC.IR.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_124 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_124 = erased
-- Once.CCC.IR.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_126 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_126
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_598
-- Once.CCC.IR.M.coerce-functor
d_coerce'45'functor_128 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_128 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_94 v0 v2
-- Once.CCC.IR.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_130 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_130 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_136
      v0 v2
-- Once.CCC.IR.M.coerce-round-trip
d_coerce'45'round'45'trip_132 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_132 = erased
-- Once.CCC.IR.M.coerce-struct
d_coerce'45'struct_134 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_134
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_266
-- Once.CCC.IR.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_136 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_136 = erased
-- Once.CCC.IR.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_138 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_138
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_272
-- Once.CCC.IR.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_140 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_140 = erased
-- Once.CCC.IR.M.coerce-μ-in
d_coerce'45'μ'45'in_142 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_142 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_746 v0 v2
-- Once.CCC.IR.M.coerce-μ-out
d_coerce'45'μ'45'out_144 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_144 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_788 v0 v1 v3
-- Once.CCC.IR.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_146 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_146 = erased
-- Once.CCC.IR.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_148 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_148 = erased
-- Once.CCC.IR.M.coerce-ν-in
d_coerce'45'ν'45'in_150 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_150
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_980
-- Once.CCC.IR.M.coerce-ν-out
d_coerce'45'ν'45'out_152 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_152
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_986
-- Once.CCC.IR.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_154 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_154 = erased
-- Once.CCC.IR.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_156 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_156 = erased
-- Once.CCC.IR.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_158 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_158 = erased
-- Once.CCC.IR.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_160 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_160 = erased
-- Once.CCC.IR.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_162 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_162 = erased
-- Once.CCC.IR.M.sem-CoIn
d_sem'45'CoIn_164 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_198
d_sem'45'CoIn_164
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1000
-- Once.CCC.IR.M.sem-CoOut
d_sem'45'CoOut_166 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_198 -> AgdaAny
d_sem'45'CoOut_166
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_990
-- Once.CCC.IR.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_168 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_168 = erased
-- Once.CCC.IR.M.sem-In
d_sem'45'In_170 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_182
d_sem'45'In_170
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_920
-- Once.CCC.IR.M.sem-In-Out
d_sem'45'In'45'Out_172 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_172 = erased
-- Once.CCC.IR.M.sem-Out
d_sem'45'Out_174 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'Out_174
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_928
-- Once.CCC.IR.M.sem-Out-In
d_sem'45'Out'45'In_176 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_176 = erased
-- Once.CCC.IR.M.sem-ana
d_sem'45'ana_178 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_198
d_sem'45'ana_178 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1024 v0 v2 v3
-- Once.CCC.IR.M.sem-case
d_sem'45'case_180 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_180 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_330 v3 v4 v5
-- Once.CCC.IR.M.sem-case-inl
d_sem'45'case'45'inl_182 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_182 = erased
-- Once.CCC.IR.M.sem-case-inr
d_sem'45'case'45'inr_184 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_184 = erased
-- Once.CCC.IR.M.sem-cata
d_sem'45'cata_186 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'cata_186 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_940 v0 v1 v3
-- Once.CCC.IR.M.sem-cata-compute
d_sem'45'cata'45'compute_188 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_188 = erased
-- Once.CCC.IR.M.sem-fmap
d_sem'45'fmap_190 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_190 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_418 v0 v3 v4
-- Once.CCC.IR.M.sem-fmap-Type
d_sem'45'fmap'45'Type_192 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_192 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_462 v0 v3
      v4
-- Once.CCC.IR.M.sem-fst
d_sem'45'fst_194 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_194 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_294 v2
-- Once.CCC.IR.M.sem-fst-pair
d_sem'45'fst'45'pair_196 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_196 = erased
-- Once.CCC.IR.M.sem-functor-coherence
d_sem'45'functor'45'coherence_198 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_198 = erased
-- Once.CCC.IR.M.sem-fuseNat
d_sem'45'fuseNat_200 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_200 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1154 v0 v1 v2 v3
      v5 v6
-- Once.CCC.IR.M.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_202 ::
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
d_sem'45'fuseNat'45'cong_202 = erased
-- Once.CCC.IR.M.sem-fuseNat-events
d_sem'45'fuseNat'45'events_204 ::
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
d_sem'45'fuseNat'45'events_204 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat'45'events_1250
      v1 v2 v3 v4 v5 v6 v8 v9
-- Once.CCC.IR.M.sem-inl
d_sem'45'inl_206 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_206 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_316
-- Once.CCC.IR.M.sem-inr
d_sem'45'inr_208 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_208 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_322
-- Once.CCC.IR.M.sem-pair
d_sem'45'pair_210 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_210 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_306 v2 v3
-- Once.CCC.IR.M.sem-para
d_sem'45'para_212 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 -> AgdaAny
d_sem'45'para_212 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_956 v0 v1 v3 v4
-- Once.CCC.IR.M.sem-snd
d_sem'45'snd_214 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_214 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_300 v2
-- Once.CCC.IR.M.sem-snd-pair
d_sem'45'snd'45'pair_216 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_216 = erased
-- Once.CCC.IR.M.sfmapSemAna
d_sfmapSemAna_218 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_218 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmapSemAna_1032 v0 v1 v3 v4
-- Once.CCC.IR.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_220 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_220 = erased
-- Once.CCC.IR.M.⟦_⟧
d_'10214'_'10215'_222 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_222 = erased
-- Once.CCC.IR.M.⟦_⟧F
d_'10214'_'10215'F_224 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_224 = erased
-- Once.CCC.IR.M.⟦μ⟧
d_'10214'μ'10215'_226 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_226 = erased
-- Once.CCC.IR.M.⟦ν⟧
d_'10214'ν'10215'_228 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_228 = erased
-- Once.CCC.IR.AllocMode
d_AllocMode_230 = ()
data T_AllocMode_230 = C_Stack_232 | C_Heap_234
-- Once.CCC.IR.LocMatchesMode
d_LocMatchesMode_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocMode_230 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_LocMatchesMode_238 = erased
-- Once.CCC.IR.Allocator
d_Allocator_240 = ()
data T_Allocator_240
  = C_Stack'45'allocator_242 | C_Dynamic'45'allocator_244
-- Once.CCC.IR.IR
d_IR_246 a0 a1 = ()
data T_IR_246
  = C_id_252 |
    C__'8728'__260 MAlonzo.Code.Once.Type.T_Type_112 T_IR_246
                   T_IR_246 |
    C_'10216'_'44'_'10217'_268 T_IR_246 T_IR_246 T_AllocMode_230 |
    C_fst_274 | C_snd_280 | C_inl_286 T_AllocMode_230 |
    C_inr_292 T_AllocMode_230 | C_case_300 T_IR_246 T_IR_246 |
    C_terminal_304 | C_initial_308 |
    C_curry_318 T_IR_246 T_AllocMode_230 | C_apply_326 | C_arr_334 |
    C_In_338 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
             T_AllocMode_230 |
    C_out'45'μ_342 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 |
    C_Cata_348 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               T_IR_246 |
    C_Para_354 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               T_IR_246 |
    C_Out_358 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 |
    C_in'45'ν_362 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                  T_AllocMode_230 |
    C_Ana_368 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
              T_IR_246 |
    C_Hylo_376 MAlonzo.Code.Once.Type.T_Functor_110
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 T_IR_246
               T_NatTr_248 |
    C_Fuse_384 MAlonzo.Code.Once.Type.T_Functor_110
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 T_IR_246
               T_NatTr_248 |
    C_free'45'heap_386 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 |
    C_const_390 MAlonzo.Code.Once.Type.T_FitsInReg_192 AgdaAny
                AgdaAny |
    C_SigOp_396 MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
-- Once.CCC.IR.NatTr
d_NatTr_248 a0 a1 = ()
data T_NatTr_248
  = C_ntId_398 | C_ntK_404 T_IR_246 | C_ntFst_412 T_NatTr_248 |
    C_ntSnd_420 T_NatTr_248 | C_ntCase_428 T_NatTr_248 T_NatTr_248 |
    C_ntInl_436 T_NatTr_248 | C_ntInr_444 T_NatTr_248 |
    C_ntPair_452 T_NatTr_248 T_NatTr_248
