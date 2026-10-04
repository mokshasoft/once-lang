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

module MAlonzo.Code.Once.Arith.SigOp.BlockSemBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Machine.WordSem
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.SigOp.BlockSemBridge.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_10
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_786
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_12 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_12 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_14 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_14 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_16 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_16
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'full'45'to'45'base_754
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-functor
d_coerce'45'functor_18 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_250 v0 v2
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_20 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_20 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_292
      v0 v2
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-round-trip
d_coerce'45'round'45'trip_22 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_22 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-struct
d_coerce'45'struct_24 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_24
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct_422
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_26 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_26 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_28 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_28
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'struct'8315''185'_428
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_30 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_30 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ-in
d_coerce'45'μ'45'in_32 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_32 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'in_886 v0 v2
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ-out
d_coerce'45'μ'45'out_34 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_34 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928 v0 v1
      v3
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_36 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_36 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_38 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_38 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-ν-in
d_coerce'45'ν'45'in_40 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_40
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-ν-out
d_coerce'45'ν'45'out_42 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_42
  = coe MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1126
-- Once.Arith.SigOp.BlockSemBridge.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_44 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_44 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.eraseᵍ
d_erase'7501'_46 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_erase'7501'_46
  = coe MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92
-- Once.Arith.SigOp.BlockSemBridge.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_48 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_48 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_50 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_50 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_52 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_52 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_54 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_54 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-CoIn
d_sem'45'CoIn_56 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_56
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1140
-- Once.Arith.SigOp.BlockSemBridge.M.sem-CoOut
d_sem'45'CoOut_58 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_58
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_1130
-- Once.Arith.SigOp.BlockSemBridge.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_60 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_60 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-In
d_sem'45'In_62 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_62
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_1060
-- Once.Arith.SigOp.BlockSemBridge.M.sem-In-Out
d_sem'45'In'45'Out_64 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_64 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-Out
d_sem'45'Out_66 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_66
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_1068
-- Once.Arith.SigOp.BlockSemBridge.M.sem-Out-In
d_sem'45'Out'45'In_68 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_68 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-ana
d_sem'45'ana_70 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_70 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1164 v0 v2 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sem-case
d_sem'45'case_72 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_72 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'case_486 v3 v4 v5
-- Once.Arith.SigOp.BlockSemBridge.M.sem-case-inl
d_sem'45'case'45'inl_74 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_74 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-case-inr
d_sem'45'case'45'inr_76 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_76 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-cata
d_sem'45'cata_78 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_78 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_1080 v0 v1 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sem-cata-compute
d_sem'45'cata'45'compute_80 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_80 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fmap
d_sem'45'fmap_82 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_82 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_574 v0 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fmap-Type
d_sem'45'fmap'45'Type_84 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_84 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap'45'Type_618 v0 v3
      v4
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fst
d_sem'45'fst_86 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_86 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'fst_450 v2
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fst-pair
d_sem'45'fst'45'pair_88 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_88 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-functor-coherence
d_sem'45'functor'45'coherence_90 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_90 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fuseNat
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
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fuseNat-cong
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
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fuseNat-events
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
-- Once.Arith.SigOp.BlockSemBridge.M.sem-inl
d_sem'45'inl_98 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_98 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inl_472
-- Once.Arith.SigOp.BlockSemBridge.M.sem-inr
d_sem'45'inr_100 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_100 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'inr_478
-- Once.Arith.SigOp.BlockSemBridge.M.sem-pair
d_sem'45'pair_102 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_102 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_462 v2 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sem-para
d_sem'45'para_104 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_104 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_1096 v0 v1 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.M.sem-snd
d_sem'45'snd_106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_106 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'snd_456 v2
-- Once.Arith.SigOp.BlockSemBridge.M.sem-snd-pair
d_sem'45'snd'45'pair_108 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_108 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.semAnaLayer
d_semAnaLayer_110 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_110 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_semAnaLayer_1170 v0 v2 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sfmapSemAna
d_sfmapSemAna_112 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_112 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sfmapSemAna_1178 v0 v1 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.M.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_114 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_114 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦_⟧
d_'10214'_'10215'_116 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_116 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦_⟧F
d_'10214'_'10215'F_118 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_118 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_120 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''7501'_120 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦μ⟧
d_'10214'μ'10215'_122 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'μ'10215'_122 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦ν⟧
d_'10214'ν'10215'_124 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'ν'10215'_124 = erased
-- Once.Arith.SigOp.BlockSemBridge._._.eval-arith-W
d_eval'45'arith'45'W_134 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_134 v0
  = coe
      MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
      (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.F
d_F_136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_F_136 v0
  = coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0)
-- Once.Arith.SigOp.BlockSemBridge._.W._%ˢ_
d__'37''738'__140 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'37''738'__140 v0
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._/ˢ_
d__'47''738'__142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'47''738'__142 v0
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._<ˢ_
d__'60''738'__144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Bool
d__'60''738'__144 v0
  = coe
      MAlonzo.Code.Once.Word.d__'60''738'__80
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._≡ʷ_
d__'8801''695'__146 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Bool
d__'8801''695'__146 ~v0 = du__'8801''695'__146
du__'8801''695'__146 :: Integer -> Integer -> Bool
du__'8801''695'__146
  = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.Arith.SigOp.BlockSemBridge._.W._⊕_
d__'8853'__148 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8853'__148 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8853'__26
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._⊖_
d__'8854'__150 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8854'__150 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8854'__32
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._⊗_
d__'8855'__152 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8855'__152 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8855'__38
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.%ˢ-else
d_'37''738''45'else_154 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_154 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.%ˢ-in-range
d_'37''738''45'in'45'range_156 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_156 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v3 v4
      v5
-- Once.Arith.SigOp.BlockSemBridge._.W.%ˢ-mid
d_'37''738''45'mid_158 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_158 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.%ˢ-negOne
d_'37''738''45'negOne_160 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_160 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.%ˢ-zero
d_'37''738''45'zero_162 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_162 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W./ˢ-else
d_'47''738''45'else_164 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_164 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W./ˢ-in-range
d_'47''738''45'in'45'range_166 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_166 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v3 v4
-- Once.Arith.SigOp.BlockSemBridge._.W./ˢ-mid
d_'47''738''45'mid_168 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_168 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W./ˢ-negOne
d_'47''738''45'negOne_170 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_170 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W./ˢ-pow2
d_'47''738''45'pow2_172 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_172 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W./ˢ-zero
d_'47''738''45'zero_174 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_174 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.0<half
d_0'60'half_176 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_176 ~v0 = du_0'60'half_176
du_0'60'half_176 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_176 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.Arith.SigOp.BlockSemBridge._.W.0<modulus
d_0'60'modulus_178 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_178 ~v0 = du_0'60'modulus_178
du_0'60'modulus_178 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_178
  = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.Arith.SigOp.BlockSemBridge._.W.0<negOne
d_0'60'negOne_180 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_180 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_426
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.1<modulus
d_1'60'modulus_182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_182 v0
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_796
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.2*n≡n+n
d_2'42'n'8801'n'43'n_184 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_184 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.2≤modulus
d_2'8804'modulus_186 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_186 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_422
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.<⇒<ᵇtrue
d_'60''8658''60''7495'true_188 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_188 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.InRange
d_InRange_190 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> ()
d_InRange_190 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.Word
d_Word_192 :: MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> ()
d_Word_192 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.fromℤ
d_fromℤ_194 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_fromℤ_194 v0
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ_20
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.fromℤ-0
d_fromℤ'45'0_196 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_196 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.fromℤ-in-range
d_fromℤ'45'in'45'range_198 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_198 v0
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_200 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_200 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.fromℤ-neg1
d_fromℤ'45'neg1_202 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_202 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.half
d_half_204 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_half_204 v0
  = coe
      MAlonzo.Code.Once.Word.d_half_48
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.half<modulus
d_half'60'modulus_206 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_206 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_430
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.half≡2^b
d_half'8801'2'94'b_208 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_208 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.half≤negOne
d_half'8804'negOne_210 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_210 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_450
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.inRange?
d_inRange'63'_212 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_212 v0
  = coe
      MAlonzo.Code.Once.Word.d_inRange'63'_62
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.intMin
d_intMin_214 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_intMin_214 v0
  = coe
      MAlonzo.Code.Once.Word.d_intMin_54
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.lit-hi
d_lit'45'hi_216 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_216 ~v0 = du_lit'45'hi_216
du_lit'45'hi_216 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'hi_216 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_654 v3
-- Once.Arith.SigOp.BlockSemBridge._.W.lit-lo
d_lit'45'lo_218 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_218 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_666
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v3 v4
-- Once.Arith.SigOp.BlockSemBridge._.W.modulus
d_modulus_220 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_modulus_220 v0
  = coe
      MAlonzo.Code.Once.Word.d_modulus_10
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_222 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_222 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.modulus≢0
d_modulus'8802'0_224 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_224 v0
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.mod∸half≡half
d_mod'8760'half'8801'half_226 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_226 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.mod≡half+half
d_mod'8801'half'43'half_228 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_228 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.negOne
d_negOne_230 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_negOne_230 v0
  = coe
      MAlonzo.Code.Once.Word.d_negOne_78
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.negOne<modulus
d_negOne'60'modulus_232 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_232 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_438
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.negOne≢0
d_negOne'8802'0_234 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_234 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.norm
d_norm_236 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_norm_236 v0
  = coe
      MAlonzo.Code.Once.Word.d_norm_16
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.norm-0
d_norm'45'0_238 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_238 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.norm-id
d_norm'45'id_240 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_240 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.sdiv2ᵏ
d_sdiv2'7503'_242 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_242 v0
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.shlᵂ
d_shl'7490'_244 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_shl'7490'_244 v0
  = coe
      MAlonzo.Code.Once.Word.d_shl'7490'_132
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.sucNegOne≡mod
d_sucNegOne'8801'mod_246 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_246 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.tdiv-neg1
d_tdiv'45'neg1_248 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_248 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.tmod-neg1
d_tmod'45'neg1_250 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_250 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.toWord
d_toWord_252 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_252 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_toWord_68
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v1
-- Once.Arith.SigOp.BlockSemBridge._.W.toWord≡fromℤ
d_toWord'8801'fromℤ_254 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_254 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.toℤ
d_toℤ_256 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_toℤ_256 v0
  = coe
      MAlonzo.Code.Once.Word.d_toℤ_50
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.toℤ-negOne
d_toℤ'45'negOne_258 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_258 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.toℤ∘fromℤ
d_toℤ'8728'fromℤ_260 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_260 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.unplus
d_unplus_262 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_262 ~v0 = du_unplus_262
du_unplus_262 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_unplus_262 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.Arith.SigOp.BlockSemBridge._.W.≡ᵇ-refl
d_'8801''7495''45'refl_264 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_264 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.≡ᵇ0-false
d_'8801''7495'0'45'false_266 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_266 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_268 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_268 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊕-neg
d_'8853''45'neg_270 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_270 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊕-neg-suc
d_'8853''45'neg'45'suc_272 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_272 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊕-normʳ
d_'8853''45'norm'691'_274 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_274 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊕≡+
d_'8853''8801''43'_276 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_276 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊖-normʳ
d_'8854''45'norm'691'_278 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_278 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊖≡∸
d_'8854''8801''8760'_280 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_280 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊗-pow2
d_'8855''45'pow2_282 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_282 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊝_
d_'8861'__284 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_'8861'__284 v0
  = coe
      MAlonzo.Code.Once.Word.d_'8861'__44
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.⊝-fromℤ
d_'8861''45'fromℤ_286 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_286 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊝-intMin
d_'8861''45'intMin_288 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_288 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.⊝-invol-norm
d_'8861''45'invol'45'norm_290 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_290 = erased
-- Once.Arith.SigOp.BlockSemBridge._.toWord
d_toWord_294 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny -> AgdaAny
d_toWord_294 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20
             (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
             (coe v2)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14 -> coe v2
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_toWord_294 (coe v0) (coe v3) (coe v5))
                    (coe d_toWord_294 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.BlockSemBridge._.project-commute
d_project'45'commute_314 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_project'45'commute_314 = erased
-- Once.Arith.SigOp.BlockSemBridge._.projectF-commute
d_projectF'45'commute_362 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projectF'45'commute_362 = erased
-- Once.Arith.SigOp.BlockSemBridge._.readLeaf-commute
d_readLeaf'45'commute_410 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLeaf'45'commute_410 = erased
-- Once.Arith.SigOp.BlockSemBridge._.readLeafF-commute
d_readLeafF'45'commute_432 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLeafF'45'commute_432 = erased
-- Once.Arith.SigOp.BlockSemBridge._.eval≡semM
d_eval'8801'semM_456 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'8801'semM_456 = erased
