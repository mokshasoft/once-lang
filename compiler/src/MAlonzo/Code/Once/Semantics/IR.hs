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

module MAlonzo.Code.Once.Semantics.IR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type

-- Once.Semantics.IR._.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_150 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_652
-- Once.Semantics.IR._.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_10 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_150 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_10 = erased
-- Once.Semantics.IR._.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_150 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_12 = erased
-- Once.Semantics.IR._.coerce-full-to-base
d_coerce'45'full'45'to'45'base_14 ::
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_14
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_616
-- Once.Semantics.IR._.coerce-functor
d_coerce'45'functor_16 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'functor_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_112 v0 v2
-- Once.Semantics.IR._.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_18 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_154
      v0 v2
-- Once.Semantics.IR._.coerce-round-trip
d_coerce'45'round'45'trip_20 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_20 = erased
-- Once.Semantics.IR._.coerce-struct
d_coerce'45'struct_22 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'struct_22
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_284
-- Once.Semantics.IR._.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_24 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_24 = erased
-- Once.Semantics.IR._.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_26 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_26
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_290
-- Once.Semantics.IR._.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_28 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_28 = erased
-- Once.Semantics.IR._.coerce-μ-in
d_coerce'45'μ'45'in_30 ::
  MAlonzo.Code.Once.Type.T_Functor_36 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_30 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_764 v0 v2
-- Once.Semantics.IR._.coerce-μ-out
d_coerce'45'μ'45'out_32 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_32 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_806 v0 v1 v3
-- Once.Semantics.IR._.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_34 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_34 = erased
-- Once.Semantics.IR._.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_36 = erased
-- Once.Semantics.IR._.coerce-ν-in
d_coerce'45'ν'45'in_38 ::
  MAlonzo.Code.Once.Type.T_Functor_36 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_38
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_998
-- Once.Semantics.IR._.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_40 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_40 = erased
-- Once.Semantics.IR._.coerce-ν-out
d_coerce'45'ν'45'out_42 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_42
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_1004
-- Once.Semantics.IR._.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_44 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_44 = erased
-- Once.Semantics.IR._.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_46 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_46 = erased
-- Once.Semantics.IR._.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_48 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_48 = erased
-- Once.Semantics.IR._.fmap-struct-coherence
d_fmap'45'struct'45'coherence_50 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_50 = erased
-- Once.Semantics.IR._.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_52 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_52 = erased
-- Once.Semantics.IR._.funext
d_funext_54 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funext_54 = erased
-- Once.Semantics.IR._.sem-CoIn
d_sem'45'CoIn_56 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'CoIn_56
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1018
-- Once.Semantics.IR._.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_58 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_58 = erased
-- Once.Semantics.IR._.sem-CoOut
d_sem'45'CoOut_60 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
d_sem'45'CoOut_60
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1008
-- Once.Semantics.IR._.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_62 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_62 = erased
-- Once.Semantics.IR._.sem-In
d_sem'45'In_64 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
d_sem'45'In_64
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_938
-- Once.Semantics.IR._.sem-In-Out
d_sem'45'In'45'Out_66 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_66 = erased
-- Once.Semantics.IR._.sem-Out
d_sem'45'Out_68 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'Out_68
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_946
-- Once.Semantics.IR._.sem-Out-In
d_sem'45'Out'45'In_70 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_70 = erased
-- Once.Semantics.IR._.sem-ana
d_sem'45'ana_72 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'ana_72 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1118 v0 v2 v3
-- Once.Semantics.IR._.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_74 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_74 = erased
-- Once.Semantics.IR._.sem-ana-bisim-anaS
d_sem'45'ana'45'bisim'45'anaS_76 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
d_sem'45'ana'45'bisim'45'anaS_76 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana'45'bisim'45'anaS_1476
      v0 v2
-- Once.Semantics.IR._.sem-ana-is-anaS-unfoldS
d_sem'45'ana'45'is'45'anaS'45'unfoldS_78 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'is'45'anaS'45'unfoldS_78 = erased
-- Once.Semantics.IR._.sem-case
d_sem'45'case_80 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_80 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_348 v3 v4 v5
-- Once.Semantics.IR._.sem-case-inl
d_sem'45'case'45'inl_82 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_82 = erased
-- Once.Semantics.IR._.sem-case-inr
d_sem'45'case'45'inr_84 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_84 = erased
-- Once.Semantics.IR._.sem-cata
d_sem'45'cata_86 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'cata_86 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_958 v0 v1 v3
-- Once.Semantics.IR._.sem-cata-In-id
d_sem'45'cata'45'In'45'id_88 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_88 = erased
-- Once.Semantics.IR._.sem-cata-compute
d_sem'45'cata'45'compute_90 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_90 = erased
-- Once.Semantics.IR._.sem-fmap
d_sem'45'fmap_92 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_92 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_436 v0 v3 v4
-- Once.Semantics.IR._.sem-fmap-Type
d_sem'45'fmap'45'Type_94 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_94 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_480 v0 v3
      v4
-- Once.Semantics.IR._.sem-fst
d_sem'45'fst_96 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_96 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_312 v2
-- Once.Semantics.IR._.sem-fst-pair
d_sem'45'fst'45'pair_98 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_98 = erased
-- Once.Semantics.IR._.sem-functor-coherence
d_sem'45'functor'45'coherence_100 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_100 = erased
-- Once.Semantics.IR._.sem-fuse
d_sem'45'fuse_102 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuse_102 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuse_1134 v0 v1 v2 v3 v5
      v6
-- Once.Semantics.IR._.sem-fuseNat
d_sem'45'fuseNat_104 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuseNat_104 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1158 v0 v1 v2 v3
      v5 v6
-- Once.Semantics.IR._.sem-hylo
d_sem'45'hylo_106 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'hylo_106 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'hylo_1180 v0 v1 v2 v3 v5
      v6
-- Once.Semantics.IR._.sem-hylo-is-fuse
d_sem'45'hylo'45'is'45'fuse_108 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'hylo'45'is'45'fuse_108 = erased
-- Once.Semantics.IR._.sem-inl
d_sem'45'inl_110 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_110 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_334
-- Once.Semantics.IR._.sem-inr
d_sem'45'inr_112 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_112 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_340
-- Once.Semantics.IR._.sem-pair
d_sem'45'pair_114 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_114 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_324 v2 v3
-- Once.Semantics.IR._.sem-para
d_sem'45'para_116 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'para_116 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_974 v0 v1 v3 v4
-- Once.Semantics.IR._.sem-snd
d_sem'45'snd_118 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_118 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_318 v2
-- Once.Semantics.IR._.sem-snd-pair
d_sem'45'snd'45'pair_120 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_120 = erased
-- Once.Semantics.IR._.sfmap-bisim
d_sfmap'45'bisim_122 ::
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__688) ->
  AgdaAny -> AgdaAny
d_sfmap'45'bisim_122 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmap'45'bisim_1414 v0 v4 v5
-- Once.Semantics.IR._.⟦_⟧
d_'10214'_'10215'_124 :: MAlonzo.Code.Once.Type.T_Type_38 -> ()
d_'10214'_'10215'_124 = erased
-- Once.Semantics.IR._.⟦_⟧F
d_'10214'_'10215'F_126 ::
  MAlonzo.Code.Once.Type.T_Functor_36 -> () -> ()
d_'10214'_'10215'F_126 = erased
-- Once.Semantics.IR._.⟦μ⟧
d_'10214'μ'10215'_128 :: MAlonzo.Code.Once.Type.T_Functor_36 -> ()
d_'10214'μ'10215'_128 = erased
-- Once.Semantics.IR._.⟦ν⟧
d_'10214'ν'10215'_130 :: MAlonzo.Code.Once.Type.T_Functor_36 -> ()
d_'10214'ν'10215'_130 = erased
-- Once.Semantics.IR.PrimSem
d_PrimSem_132 = ()
newtype T_PrimSem_132
  = C_constructor_146 (MAlonzo.Code.Once.Type.T_Type_38 ->
                       MAlonzo.Code.Once.Type.T_Type_38 ->
                       MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny)
-- Once.Semantics.IR.PrimSem.evalPrim
d_evalPrim_144 ::
  T_PrimSem_132 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_evalPrim_144 v0
  = case coe v0 of
      C_constructor_146 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.IR.eval
d_eval_152 ::
  T_PrimSem_132 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> AgdaAny -> AgdaAny
d_eval_152 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.CCC.IR.C_id_16 -> coe v4
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v6 v8 v9
        -> coe
             d_eval_152 (coe v0) (coe v6) (coe v2) (coe v8)
             (coe d_eval_152 (coe v0) (coe v1) (coe v6) (coe v9) (coe v4))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v8 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__52 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_eval_152 (coe v0) (coe v1) (coe v11) (coe v8) (coe v4))
                    (coe d_eval_152 (coe v0) (coe v1) (coe v12) (coe v9) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_38
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8 -> coe v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_snd_44
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8 -> coe v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v7
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4)
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v7
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
      MAlonzo.Code.Once.CCC.IR.C_case_64 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__54 v10 v11
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe d_eval_152 (coe v0) (coe v10) (coe v2) (coe v8) (coe v12)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> coe d_eval_152 (coe v0) (coe v11) (coe v2) (coe v9) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v11 v12 v13
               -> coe
                    (\ v14 ->
                       d_eval_152
                         (coe v0)
                         (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v1) (coe v11))
                         (coe v13) (coe v9)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v14)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_90
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9 -> coe v8 v9
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_arr_98 -> coe v4
      MAlonzo.Code.Once.CCC.IR.C_In_102 v6 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_938 (coe v8)
                    (coe
                       MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_112 (coe v8)
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v7
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_154
                    (coe v7)
                    (coe
                       MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_946 (coe v7)
                       (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v6 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v9
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_958 v9 v6
                    (\ v10 ->
                       d_eval_152
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_90 (coe v9) (coe v2))
                         (coe v2) (coe v8)
                         (coe
                            MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_154
                            (coe v9) (coe v10)))
                    v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v6 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v9
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_974 (coe v9)
                    (coe v6)
                    (coe
                       (\ v10 ->
                          d_eval_152
                            (coe v0)
                            (coe
                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_90 (coe v9)
                               (coe MAlonzo.Code.Once.Type.C__'42'__52 (coe v1) (coe v2)))
                            (coe v2) (coe v8)
                            (coe
                               MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_154
                               (coe v9) (coe v10))))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v7
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_154
                    (coe v7)
                    (coe
                       MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1008 (coe v7)
                       (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v6 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v8
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1018 (coe v8)
                    (coe
                       MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_112 (coe v8)
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v6 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_ν'45'type_62 v9
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1118 (coe v9)
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_112 (coe v9)
                            (coe
                               d_eval_152 (coe v0) (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_90 (coe v9) (coe v1))
                               (coe v8) (coe v10))))
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v5 v7 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v12
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'hylo_1180 v5 v12 v7 v8
                    (\ v13 ->
                       d_eval_152
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_90 (coe v5) (coe v2))
                         (coe v2) (coe v10)
                         (coe
                            MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_154
                            (coe v5) (coe v13)))
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_112 (coe v5)
                         (coe
                            d_eval_152 (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_90 (coe v5) (coe v1))
                            (coe v11) (coe v13)))
                    v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v5 v7 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_60 v12
               -> coe
                    MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuse_1134 v5 v12 v7 v8
                    (\ v13 ->
                       d_eval_152
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_90 (coe v5) (coe v2))
                         (coe v2) (coe v10)
                         (coe
                            MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_154
                            (coe v5) (coe v13)))
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_112 (coe v5)
                         (coe
                            d_eval_152 (coe v0)
                            (coe
                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_90 (coe v12) (coe v1))
                            (coe
                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_90 (coe v5) (coe v1))
                            (coe v11)
                            (coe
                               MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_154
                               (coe v12) (coe v13))))
                    v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v5 -> coe v4
      MAlonzo.Code.Once.CCC.IR.C_Prim_156 v7
        -> coe d_evalPrim_144 v0 v1 v2 v7 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.IR.defaultEvalPrim
d_defaultEvalPrim_356
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.IR.defaultEvalPrim"
-- Once.Semantics.IR.defaultPrimSem
d_defaultPrimSem_358 :: T_PrimSem_132
d_defaultPrimSem_358
  = coe C_constructor_146 (coe d_defaultEvalPrim_356)
-- Once.Semantics.IR.eval′
d_eval'8242'_364 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 -> AgdaAny -> AgdaAny
d_eval'8242'_364 v0 v1
  = coe d_eval_152 (coe d_defaultPrimSem_358) (coe v0) (coe v1)
