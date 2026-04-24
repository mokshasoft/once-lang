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

module MAlonzo.Code.Once.CCC.SigOp.Info where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.SigOp.Info.I.coerce-base-to-full
d_coerce'45'base'45'to'45'full_10 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_10
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_648
-- Once.CCC.SigOp.Info.I.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_12 = erased
-- Once.CCC.SigOp.Info.I.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_14 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_14 = erased
-- Once.CCC.SigOp.Info.I.coerce-full-to-base
d_coerce'45'full'45'to'45'base_16 ::
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_16
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_612
-- Once.CCC.SigOp.Info.I.coerce-functor
d_coerce'45'functor_18 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'functor_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 v0 v2
-- Once.CCC.SigOp.Info.I.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_20 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_20 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      v0 v2
-- Once.CCC.SigOp.Info.I.coerce-round-trip
d_coerce'45'round'45'trip_22 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_22 = erased
-- Once.CCC.SigOp.Info.I.coerce-struct
d_coerce'45'struct_24 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'struct_24
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_280
-- Once.CCC.SigOp.Info.I.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_26 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_26 = erased
-- Once.CCC.SigOp.Info.I.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_28 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_28
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_286
-- Once.CCC.SigOp.Info.I.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_30 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_30 = erased
-- Once.CCC.SigOp.Info.I.coerce-μ-in
d_coerce'45'μ'45'in_32 ::
  MAlonzo.Code.Once.Type.T_Functor_124 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_32 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_760 v0 v2
-- Once.CCC.SigOp.Info.I.coerce-μ-out
d_coerce'45'μ'45'out_34 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_34 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_802 v0 v1 v3
-- Once.CCC.SigOp.Info.I.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_36 = erased
-- Once.CCC.SigOp.Info.I.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_38 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_38 = erased
-- Once.CCC.SigOp.Info.I.coerce-ν-in
d_coerce'45'ν'45'in_40 ::
  MAlonzo.Code.Once.Type.T_Functor_124 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_40
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_994
-- Once.CCC.SigOp.Info.I.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_42 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_42 = erased
-- Once.CCC.SigOp.Info.I.coerce-ν-out
d_coerce'45'ν'45'out_44 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_44
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_1000
-- Once.CCC.SigOp.Info.I.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_46 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_46 = erased
-- Once.CCC.SigOp.Info.I.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_48 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_48 = erased
-- Once.CCC.SigOp.Info.I.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_50 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_50 = erased
-- Once.CCC.SigOp.Info.I.fmap-struct-coherence
d_fmap'45'struct'45'coherence_52 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_52 = erased
-- Once.CCC.SigOp.Info.I.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_54 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_54 = erased
-- Once.CCC.SigOp.Info.I.funext
d_funext_56 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funext_56 = erased
-- Once.CCC.SigOp.Info.I.sem-CoIn
d_sem'45'CoIn_58 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'CoIn_58
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1014
-- Once.CCC.SigOp.Info.I.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_60 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_60 = erased
-- Once.CCC.SigOp.Info.I.sem-CoOut
d_sem'45'CoOut_62 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
d_sem'45'CoOut_62
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1004
-- Once.CCC.SigOp.Info.I.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_64 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_64 = erased
-- Once.CCC.SigOp.Info.I.sem-In
d_sem'45'In_66 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
d_sem'45'In_66
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_934
-- Once.CCC.SigOp.Info.I.sem-In-Out
d_sem'45'In'45'Out_68 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_68 = erased
-- Once.CCC.SigOp.Info.I.sem-Out
d_sem'45'Out_70 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'Out_70
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_942
-- Once.CCC.SigOp.Info.I.sem-Out-In
d_sem'45'Out'45'In_72 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_72 = erased
-- Once.CCC.SigOp.Info.I.sem-ana
d_sem'45'ana_74 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'ana_74 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114 v0 v2 v3
-- Once.CCC.SigOp.Info.I.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_76 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_76 = erased
-- Once.CCC.SigOp.Info.I.sem-ana-bisim-anaS
d_sem'45'ana'45'bisim'45'anaS_78 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
d_sem'45'ana'45'bisim'45'anaS_78 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana'45'bisim'45'anaS_1472
      v0 v2
-- Once.CCC.SigOp.Info.I.sem-ana-is-anaS-unfoldS
d_sem'45'ana'45'is'45'anaS'45'unfoldS_80 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'is'45'anaS'45'unfoldS_80 = erased
-- Once.CCC.SigOp.Info.I.sem-case
d_sem'45'case_82 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_82 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_344 v3 v4 v5
-- Once.CCC.SigOp.Info.I.sem-case-inl
d_sem'45'case'45'inl_84 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_84 = erased
-- Once.CCC.SigOp.Info.I.sem-case-inr
d_sem'45'case'45'inr_86 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_86 = erased
-- Once.CCC.SigOp.Info.I.sem-cata
d_sem'45'cata_88 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'cata_88 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v0 v1 v3
-- Once.CCC.SigOp.Info.I.sem-cata-In-id
d_sem'45'cata'45'In'45'id_90 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_90 = erased
-- Once.CCC.SigOp.Info.I.sem-cata-compute
d_sem'45'cata'45'compute_92 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_92 = erased
-- Once.CCC.SigOp.Info.I.sem-fmap
d_sem'45'fmap_94 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_94 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 v0 v3 v4
-- Once.CCC.SigOp.Info.I.sem-fmap-Type
d_sem'45'fmap'45'Type_96 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_96 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_476 v0 v3
      v4
-- Once.CCC.SigOp.Info.I.sem-fst
d_sem'45'fst_98 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_98 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_308 v2
-- Once.CCC.SigOp.Info.I.sem-fst-pair
d_sem'45'fst'45'pair_100 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_100 = erased
-- Once.CCC.SigOp.Info.I.sem-functor-coherence
d_sem'45'functor'45'coherence_102 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_102 = erased
-- Once.CCC.SigOp.Info.I.sem-fuse
d_sem'45'fuse_104 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuse_104 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuse_1130 v0 v1 v2 v3 v5
      v6
-- Once.CCC.SigOp.Info.I.sem-fuseNat
d_sem'45'fuseNat_106 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuseNat_106 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1154 v0 v1 v2 v3
      v5 v6
-- Once.CCC.SigOp.Info.I.sem-hylo
d_sem'45'hylo_108 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'hylo_108 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'hylo_1176 v0 v1 v2 v3 v5
      v6
-- Once.CCC.SigOp.Info.I.sem-hylo-is-fuse
d_sem'45'hylo'45'is'45'fuse_110 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'hylo'45'is'45'fuse_110 = erased
-- Once.CCC.SigOp.Info.I.sem-inl
d_sem'45'inl_112 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_112 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_330
-- Once.CCC.SigOp.Info.I.sem-inr
d_sem'45'inr_114 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_114 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_336
-- Once.CCC.SigOp.Info.I.sem-pair
d_sem'45'pair_116 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_116 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320 v2 v3
-- Once.CCC.SigOp.Info.I.sem-para
d_sem'45'para_118 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'para_118 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_970 v0 v1 v3 v4
-- Once.CCC.SigOp.Info.I.sem-snd
d_sem'45'snd_120 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_120 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_314 v2
-- Once.CCC.SigOp.Info.I.sem-snd-pair
d_sem'45'snd'45'pair_122 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_122 = erased
-- Once.CCC.SigOp.Info.I.sfmap-bisim
d_sfmap'45'bisim_124 ::
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__688) ->
  AgdaAny -> AgdaAny
d_sfmap'45'bisim_124 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmap'45'bisim_1410 v0 v4 v5
-- Once.CCC.SigOp.Info.I.⟦_⟧
d_'10214'_'10215'_126 :: MAlonzo.Code.Once.Type.T_Type_126 -> ()
d_'10214'_'10215'_126 = erased
-- Once.CCC.SigOp.Info.I.⟦_⟧F
d_'10214'_'10215'F_128 ::
  MAlonzo.Code.Once.Type.T_Functor_124 -> () -> ()
d_'10214'_'10215'F_128 = erased
-- Once.CCC.SigOp.Info.I.⟦μ⟧
d_'10214'μ'10215'_130 :: MAlonzo.Code.Once.Type.T_Functor_124 -> ()
d_'10214'μ'10215'_130 = erased
-- Once.CCC.SigOp.Info.I.⟦ν⟧
d_'10214'ν'10215'_132 :: MAlonzo.Code.Once.Type.T_Functor_124 -> ()
d_'10214'ν'10215'_132 = erased
-- Once.CCC.SigOp.Info.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_136 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_136
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_648
-- Once.CCC.SigOp.Info.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_138 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_138 = erased
-- Once.CCC.SigOp.Info.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_140 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_140 = erased
-- Once.CCC.SigOp.Info.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_142 ::
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_142
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_612
-- Once.CCC.SigOp.Info.M.coerce-functor
d_coerce'45'functor_144 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'functor_144 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 v0 v2
-- Once.CCC.SigOp.Info.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_146 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_146 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      v0 v2
-- Once.CCC.SigOp.Info.M.coerce-round-trip
d_coerce'45'round'45'trip_148 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_148 = erased
-- Once.CCC.SigOp.Info.M.coerce-struct
d_coerce'45'struct_150 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'struct_150
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_280
-- Once.CCC.SigOp.Info.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_152 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_152 = erased
-- Once.CCC.SigOp.Info.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_154 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_154
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_286
-- Once.CCC.SigOp.Info.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_156 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_156 = erased
-- Once.CCC.SigOp.Info.M.coerce-μ-in
d_coerce'45'μ'45'in_158 ::
  MAlonzo.Code.Once.Type.T_Functor_124 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_158 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_760 v0 v2
-- Once.CCC.SigOp.Info.M.coerce-μ-out
d_coerce'45'μ'45'out_160 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_160 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_802 v0 v1 v3
-- Once.CCC.SigOp.Info.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_162 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_162 = erased
-- Once.CCC.SigOp.Info.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_164 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_164 = erased
-- Once.CCC.SigOp.Info.M.coerce-ν-in
d_coerce'45'ν'45'in_166 ::
  MAlonzo.Code.Once.Type.T_Functor_124 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_166
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_994
-- Once.CCC.SigOp.Info.M.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_168 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_168 = erased
-- Once.CCC.SigOp.Info.M.coerce-ν-out
d_coerce'45'ν'45'out_170 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_170
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_1000
-- Once.CCC.SigOp.Info.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_172 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_172 = erased
-- Once.CCC.SigOp.Info.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_174 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_174 = erased
-- Once.CCC.SigOp.Info.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_176 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_176 = erased
-- Once.CCC.SigOp.Info.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_178 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_178 = erased
-- Once.CCC.SigOp.Info.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_180 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_180 = erased
-- Once.CCC.SigOp.Info.M.funext
d_funext_182 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funext_182 = erased
-- Once.CCC.SigOp.Info.M.sem-CoIn
d_sem'45'CoIn_184 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'CoIn_184
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1014
-- Once.CCC.SigOp.Info.M.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_186 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_186 = erased
-- Once.CCC.SigOp.Info.M.sem-CoOut
d_sem'45'CoOut_188 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
d_sem'45'CoOut_188
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1004
-- Once.CCC.SigOp.Info.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_190 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_190 = erased
-- Once.CCC.SigOp.Info.M.sem-In
d_sem'45'In_192 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
d_sem'45'In_192
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_934
-- Once.CCC.SigOp.Info.M.sem-In-Out
d_sem'45'In'45'Out_194 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_194 = erased
-- Once.CCC.SigOp.Info.M.sem-Out
d_sem'45'Out_196 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'Out_196
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_942
-- Once.CCC.SigOp.Info.M.sem-Out-In
d_sem'45'Out'45'In_198 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_198 = erased
-- Once.CCC.SigOp.Info.M.sem-ana
d_sem'45'ana_200 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'ana_200 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114 v0 v2 v3
-- Once.CCC.SigOp.Info.M.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_202 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_202 = erased
-- Once.CCC.SigOp.Info.M.sem-ana-bisim-anaS
d_sem'45'ana'45'bisim'45'anaS_204 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
d_sem'45'ana'45'bisim'45'anaS_204 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana'45'bisim'45'anaS_1472
      v0 v2
-- Once.CCC.SigOp.Info.M.sem-ana-is-anaS-unfoldS
d_sem'45'ana'45'is'45'anaS'45'unfoldS_206 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'is'45'anaS'45'unfoldS_206 = erased
-- Once.CCC.SigOp.Info.M.sem-case
d_sem'45'case_208 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_208 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_344 v3 v4 v5
-- Once.CCC.SigOp.Info.M.sem-case-inl
d_sem'45'case'45'inl_210 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_210 = erased
-- Once.CCC.SigOp.Info.M.sem-case-inr
d_sem'45'case'45'inr_212 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_212 = erased
-- Once.CCC.SigOp.Info.M.sem-cata
d_sem'45'cata_214 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'cata_214 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v0 v1 v3
-- Once.CCC.SigOp.Info.M.sem-cata-In-id
d_sem'45'cata'45'In'45'id_216 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_216 = erased
-- Once.CCC.SigOp.Info.M.sem-cata-compute
d_sem'45'cata'45'compute_218 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_218 = erased
-- Once.CCC.SigOp.Info.M.sem-fmap
d_sem'45'fmap_220 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_220 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 v0 v3 v4
-- Once.CCC.SigOp.Info.M.sem-fmap-Type
d_sem'45'fmap'45'Type_222 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_222 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_476 v0 v3
      v4
-- Once.CCC.SigOp.Info.M.sem-fst
d_sem'45'fst_224 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_224 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_308 v2
-- Once.CCC.SigOp.Info.M.sem-fst-pair
d_sem'45'fst'45'pair_226 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_226 = erased
-- Once.CCC.SigOp.Info.M.sem-functor-coherence
d_sem'45'functor'45'coherence_228 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_228 = erased
-- Once.CCC.SigOp.Info.M.sem-fuse
d_sem'45'fuse_230 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuse_230 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuse_1130 v0 v1 v2 v3 v5
      v6
-- Once.CCC.SigOp.Info.M.sem-fuseNat
d_sem'45'fuseNat_232 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuseNat_232 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1154 v0 v1 v2 v3
      v5 v6
-- Once.CCC.SigOp.Info.M.sem-hylo
d_sem'45'hylo_234 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'hylo_234 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'hylo_1176 v0 v1 v2 v3 v5
      v6
-- Once.CCC.SigOp.Info.M.sem-hylo-is-fuse
d_sem'45'hylo'45'is'45'fuse_236 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'hylo'45'is'45'fuse_236 = erased
-- Once.CCC.SigOp.Info.M.sem-inl
d_sem'45'inl_238 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_238 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_330
-- Once.CCC.SigOp.Info.M.sem-inr
d_sem'45'inr_240 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_240 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_336
-- Once.CCC.SigOp.Info.M.sem-pair
d_sem'45'pair_242 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_242 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320 v2 v3
-- Once.CCC.SigOp.Info.M.sem-para
d_sem'45'para_244 ::
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'para_244 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_970 v0 v1 v3 v4
-- Once.CCC.SigOp.Info.M.sem-snd
d_sem'45'snd_246 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_246 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_314 v2
-- Once.CCC.SigOp.Info.M.sem-snd-pair
d_sem'45'snd'45'pair_248 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_248 = erased
-- Once.CCC.SigOp.Info.M.sfmap-bisim
d_sfmap'45'bisim_250 ::
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  MAlonzo.Code.Once.Type.T_Functor_124 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__688) ->
  AgdaAny -> AgdaAny
d_sfmap'45'bisim_250 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmap'45'bisim_1410 v0 v4 v5
-- Once.CCC.SigOp.Info.M.⟦_⟧
d_'10214'_'10215'_252 :: MAlonzo.Code.Once.Type.T_Type_126 -> ()
d_'10214'_'10215'_252 = erased
-- Once.CCC.SigOp.Info.M.⟦_⟧F
d_'10214'_'10215'F_254 ::
  MAlonzo.Code.Once.Type.T_Functor_124 -> () -> ()
d_'10214'_'10215'F_254 = erased
-- Once.CCC.SigOp.Info.M.⟦μ⟧
d_'10214'μ'10215'_256 :: MAlonzo.Code.Once.Type.T_Functor_124 -> ()
d_'10214'μ'10215'_256 = erased
-- Once.CCC.SigOp.Info.M.⟦ν⟧
d_'10214'ν'10215'_258 :: MAlonzo.Code.Once.Type.T_Functor_124 -> ()
d_'10214'ν'10215'_258 = erased
-- Once.CCC.SigOp.Info.SigOpInfo
d_SigOpInfo_264 a0 a1 = ()
data T_SigOpInfo_264
  = C_mk'45'info_282 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- Once.CCC.SigOp.Info.SigOpInfo.name
d_name_276 ::
  T_SigOpInfo_264 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_name_276 v0
  = case coe v0 of
      C_mk'45'info_282 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SigOp.Info.SigOpInfo.semI
d_semI_278 :: T_SigOpInfo_264 -> AgdaAny -> AgdaAny
d_semI_278 v0
  = case coe v0 of
      C_mk'45'info_282 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SigOp.Info.SigOpInfo.semM
d_semM_280 :: T_SigOpInfo_264 -> AgdaAny -> AgdaAny
d_semM_280 v0
  = case coe v0 of
      C_mk'45'info_282 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SigOp.Info._≟SigOpInfo-name_
d__'8799'SigOpInfo'45'name__292 ::
  T_SigOpInfo_264 ->
  T_SigOpInfo_264 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'SigOpInfo'45'name__292 v0 v1
  = coe
      MAlonzo.Code.Data.String.Properties.d__'8799'__54
      (coe d_name_276 (coe v0)) (coe d_name_276 (coe v1))
-- Once.CCC.SigOp.Info.sigOpInfo-name-coherence
d_sigOpInfo'45'name'45'coherence_306
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.SigOp.Info.sigOpInfo-name-coherence"
-- Once.CCC.SigOp.Info._≟SigOpInfo_
d__'8799'SigOpInfo__316 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  T_SigOpInfo_264 ->
  T_SigOpInfo_264 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'SigOpInfo__316 ~v0 ~v1 v2 v3
  = du__'8799'SigOpInfo__316 v2 v3
du__'8799'SigOpInfo__316 ::
  T_SigOpInfo_264 ->
  T_SigOpInfo_264 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'SigOpInfo__316 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe d_name_276 (coe v0)))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                 (coe d_name_276 (coe v0)) (coe d_name_276 (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
