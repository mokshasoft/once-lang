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

module MAlonzo.Code.Once.Arith.SigOp.Block where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.SigOp.Block.W._⊕_
d__'8853'__10 :: Integer -> Integer -> Integer
d__'8853'__10
  = coe MAlonzo.Code.Once.Word.d__'8853'__24 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._⊖_
d__'8854'__12 :: Integer -> Integer -> Integer
d__'8854'__12
  = coe MAlonzo.Code.Once.Word.d__'8854'__30 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._⊗_
d__'8855'__14 :: Integer -> Integer -> Integer
d__'8855'__14
  = coe MAlonzo.Code.Once.Word.d__'8855'__36 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.Word
d_Word_16 :: ()
d_Word_16 = erased
-- Once.Arith.SigOp.Block.W.fromℤ
d_fromℤ_18 :: Integer -> Integer
d_fromℤ_18
  = coe MAlonzo.Code.Once.Word.d_fromℤ_18 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.modulus
d_modulus_20 :: Integer
d_modulus_20
  = coe MAlonzo.Code.Once.Word.d_modulus_8 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.modulus≢0
d_modulus'8802'0_22 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_22
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_10 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.norm
d_norm_24 :: Integer -> Integer
d_norm_24
  = coe MAlonzo.Code.Once.Word.d_norm_14 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.⊝_
d_'8861'__26 :: Integer -> Integer
d_'8861'__26
  = coe MAlonzo.Code.Once.Word.d_'8861'__42 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.I.coerce-base-to-full
d_coerce'45'base'45'to'45'full_30 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_30
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_648
-- Once.Arith.SigOp.Block.I.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_32 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_32 = erased
-- Once.Arith.SigOp.Block.I.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_34 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_34 = erased
-- Once.Arith.SigOp.Block.I.coerce-full-to-base
d_coerce'45'full'45'to'45'base_36 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_36
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_612
-- Once.Arith.SigOp.Block.I.coerce-functor
d_coerce'45'functor_38 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_38 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 v0 v2
-- Once.Arith.SigOp.Block.I.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_40 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_40 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      v0 v2
-- Once.Arith.SigOp.Block.I.coerce-round-trip
d_coerce'45'round'45'trip_42 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_42 = erased
-- Once.Arith.SigOp.Block.I.coerce-struct
d_coerce'45'struct_44 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_44
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_280
-- Once.Arith.SigOp.Block.I.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_46 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_46 = erased
-- Once.Arith.SigOp.Block.I.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_48 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_48
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_286
-- Once.Arith.SigOp.Block.I.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_50 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_50 = erased
-- Once.Arith.SigOp.Block.I.coerce-μ-in
d_coerce'45'μ'45'in_52 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_52 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_760 v0 v2
-- Once.Arith.SigOp.Block.I.coerce-μ-out
d_coerce'45'μ'45'out_54 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_54 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_802 v0 v1 v3
-- Once.Arith.SigOp.Block.I.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_56 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_56 = erased
-- Once.Arith.SigOp.Block.I.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_58 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_58 = erased
-- Once.Arith.SigOp.Block.I.coerce-ν-in
d_coerce'45'ν'45'in_60 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_60
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_994
-- Once.Arith.SigOp.Block.I.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_62 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_62 = erased
-- Once.Arith.SigOp.Block.I.coerce-ν-out
d_coerce'45'ν'45'out_64 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_64
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_1000
-- Once.Arith.SigOp.Block.I.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_66 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_66 = erased
-- Once.Arith.SigOp.Block.I.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_68 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_68 = erased
-- Once.Arith.SigOp.Block.I.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_70 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_70 = erased
-- Once.Arith.SigOp.Block.I.fmap-struct-coherence
d_fmap'45'struct'45'coherence_72 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_72 = erased
-- Once.Arith.SigOp.Block.I.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_74 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_74 = erased
-- Once.Arith.SigOp.Block.I.funext
d_funext_76 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funext_76 = erased
-- Once.Arith.SigOp.Block.I.sem-CoIn
d_sem'45'CoIn_78 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'CoIn_78
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1014
-- Once.Arith.SigOp.Block.I.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_80 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_80 = erased
-- Once.Arith.SigOp.Block.I.sem-CoOut
d_sem'45'CoOut_82 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
d_sem'45'CoOut_82
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1004
-- Once.Arith.SigOp.Block.I.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_84 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_84 = erased
-- Once.Arith.SigOp.Block.I.sem-In
d_sem'45'In_86 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
d_sem'45'In_86
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_934
-- Once.Arith.SigOp.Block.I.sem-In-Out
d_sem'45'In'45'Out_88 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_88 = erased
-- Once.Arith.SigOp.Block.I.sem-Out
d_sem'45'Out_90 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'Out_90
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_942
-- Once.Arith.SigOp.Block.I.sem-Out-In
d_sem'45'Out'45'In_92 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_92 = erased
-- Once.Arith.SigOp.Block.I.sem-ana
d_sem'45'ana_94 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'ana_94 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114 v0 v2 v3
-- Once.Arith.SigOp.Block.I.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_96 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_96 = erased
-- Once.Arith.SigOp.Block.I.sem-ana-bisim-anaS
d_sem'45'ana'45'bisim'45'anaS_98 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
d_sem'45'ana'45'bisim'45'anaS_98 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana'45'bisim'45'anaS_1472
      v0 v2
-- Once.Arith.SigOp.Block.I.sem-ana-is-anaS-unfoldS
d_sem'45'ana'45'is'45'anaS'45'unfoldS_100 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'is'45'anaS'45'unfoldS_100 = erased
-- Once.Arith.SigOp.Block.I.sem-case
d_sem'45'case_102 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_102 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_344 v3 v4 v5
-- Once.Arith.SigOp.Block.I.sem-case-inl
d_sem'45'case'45'inl_104 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_104 = erased
-- Once.Arith.SigOp.Block.I.sem-case-inr
d_sem'45'case'45'inr_106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_106 = erased
-- Once.Arith.SigOp.Block.I.sem-cata
d_sem'45'cata_108 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'cata_108 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v0 v1 v3
-- Once.Arith.SigOp.Block.I.sem-cata-In-id
d_sem'45'cata'45'In'45'id_110 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_110 = erased
-- Once.Arith.SigOp.Block.I.sem-cata-compute
d_sem'45'cata'45'compute_112 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_112 = erased
-- Once.Arith.SigOp.Block.I.sem-fmap
d_sem'45'fmap_114 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_114 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 v0 v3 v4
-- Once.Arith.SigOp.Block.I.sem-fmap-Type
d_sem'45'fmap'45'Type_116 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_116 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_476 v0 v3
      v4
-- Once.Arith.SigOp.Block.I.sem-fst
d_sem'45'fst_118 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_118 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_308 v2
-- Once.Arith.SigOp.Block.I.sem-fst-pair
d_sem'45'fst'45'pair_120 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_120 = erased
-- Once.Arith.SigOp.Block.I.sem-functor-coherence
d_sem'45'functor'45'coherence_122 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_122 = erased
-- Once.Arith.SigOp.Block.I.sem-fuse
d_sem'45'fuse_124 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuse_124 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuse_1130 v0 v1 v2 v3 v5
      v6
-- Once.Arith.SigOp.Block.I.sem-fuseNat
d_sem'45'fuseNat_126 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuseNat_126 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1154 v0 v1 v2 v3
      v5 v6
-- Once.Arith.SigOp.Block.I.sem-hylo
d_sem'45'hylo_128 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'hylo_128 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'hylo_1176 v0 v1 v2 v3 v5
      v6
-- Once.Arith.SigOp.Block.I.sem-hylo-is-fuse
d_sem'45'hylo'45'is'45'fuse_130 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'hylo'45'is'45'fuse_130 = erased
-- Once.Arith.SigOp.Block.I.sem-inl
d_sem'45'inl_132 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_132 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_330
-- Once.Arith.SigOp.Block.I.sem-inr
d_sem'45'inr_134 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_134 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_336
-- Once.Arith.SigOp.Block.I.sem-pair
d_sem'45'pair_136 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_136 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320 v2 v3
-- Once.Arith.SigOp.Block.I.sem-para
d_sem'45'para_138 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'para_138 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_970 v0 v1 v3 v4
-- Once.Arith.SigOp.Block.I.sem-snd
d_sem'45'snd_140 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_140 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_314 v2
-- Once.Arith.SigOp.Block.I.sem-snd-pair
d_sem'45'snd'45'pair_142 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_142 = erased
-- Once.Arith.SigOp.Block.I.sfmap-bisim
d_sfmap'45'bisim_144 ::
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__688) ->
  AgdaAny -> AgdaAny
d_sfmap'45'bisim_144 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmap'45'bisim_1410 v0 v4 v5
-- Once.Arith.SigOp.Block.I.⟦_⟧
d_'10214'_'10215'_146 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_146 = erased
-- Once.Arith.SigOp.Block.I.⟦_⟧F
d_'10214'_'10215'F_148 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_148 = erased
-- Once.Arith.SigOp.Block.I.⟦μ⟧
d_'10214'μ'10215'_150 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'μ'10215'_150 = erased
-- Once.Arith.SigOp.Block.I.⟦ν⟧
d_'10214'ν'10215'_152 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'ν'10215'_152 = erased
-- Once.Arith.SigOp.Block.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_156 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_156
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_648
-- Once.Arith.SigOp.Block.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_158 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_158 = erased
-- Once.Arith.SigOp.Block.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_160 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_160 = erased
-- Once.Arith.SigOp.Block.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_162 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_162
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_612
-- Once.Arith.SigOp.Block.M.coerce-functor
d_coerce'45'functor_164 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_164 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 v0 v2
-- Once.Arith.SigOp.Block.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_166 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_166 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      v0 v2
-- Once.Arith.SigOp.Block.M.coerce-round-trip
d_coerce'45'round'45'trip_168 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_168 = erased
-- Once.Arith.SigOp.Block.M.coerce-struct
d_coerce'45'struct_170 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_170
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_280
-- Once.Arith.SigOp.Block.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_172 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_172 = erased
-- Once.Arith.SigOp.Block.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_174 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_174
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_286
-- Once.Arith.SigOp.Block.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_176 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_176 = erased
-- Once.Arith.SigOp.Block.M.coerce-μ-in
d_coerce'45'μ'45'in_178 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_178 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_760 v0 v2
-- Once.Arith.SigOp.Block.M.coerce-μ-out
d_coerce'45'μ'45'out_180 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_180 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_802 v0 v1 v3
-- Once.Arith.SigOp.Block.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_182 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_182 = erased
-- Once.Arith.SigOp.Block.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_184 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_184 = erased
-- Once.Arith.SigOp.Block.M.coerce-ν-in
d_coerce'45'ν'45'in_186 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_186
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_994
-- Once.Arith.SigOp.Block.M.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_188 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_188 = erased
-- Once.Arith.SigOp.Block.M.coerce-ν-out
d_coerce'45'ν'45'out_190 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_190
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_1000
-- Once.Arith.SigOp.Block.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_192 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_192 = erased
-- Once.Arith.SigOp.Block.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_194 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_194 = erased
-- Once.Arith.SigOp.Block.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_196 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_196 = erased
-- Once.Arith.SigOp.Block.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_198 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_198 = erased
-- Once.Arith.SigOp.Block.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_200 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_200 = erased
-- Once.Arith.SigOp.Block.M.funext
d_funext_202 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funext_202 = erased
-- Once.Arith.SigOp.Block.M.sem-CoIn
d_sem'45'CoIn_204 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'CoIn_204
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1014
-- Once.Arith.SigOp.Block.M.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_206 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_206 = erased
-- Once.Arith.SigOp.Block.M.sem-CoOut
d_sem'45'CoOut_208 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
d_sem'45'CoOut_208
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1004
-- Once.Arith.SigOp.Block.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_210 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_210 = erased
-- Once.Arith.SigOp.Block.M.sem-In
d_sem'45'In_212 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
d_sem'45'In_212
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_934
-- Once.Arith.SigOp.Block.M.sem-In-Out
d_sem'45'In'45'Out_214 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_214 = erased
-- Once.Arith.SigOp.Block.M.sem-Out
d_sem'45'Out_216 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'Out_216
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_942
-- Once.Arith.SigOp.Block.M.sem-Out-In
d_sem'45'Out'45'In_218 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_218 = erased
-- Once.Arith.SigOp.Block.M.sem-ana
d_sem'45'ana_220 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'ana_220 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114 v0 v2 v3
-- Once.Arith.SigOp.Block.M.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_222 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_222 = erased
-- Once.Arith.SigOp.Block.M.sem-ana-bisim-anaS
d_sem'45'ana'45'bisim'45'anaS_224 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
d_sem'45'ana'45'bisim'45'anaS_224 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana'45'bisim'45'anaS_1472
      v0 v2
-- Once.Arith.SigOp.Block.M.sem-ana-is-anaS-unfoldS
d_sem'45'ana'45'is'45'anaS'45'unfoldS_226 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'is'45'anaS'45'unfoldS_226 = erased
-- Once.Arith.SigOp.Block.M.sem-case
d_sem'45'case_228 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_228 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_344 v3 v4 v5
-- Once.Arith.SigOp.Block.M.sem-case-inl
d_sem'45'case'45'inl_230 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_230 = erased
-- Once.Arith.SigOp.Block.M.sem-case-inr
d_sem'45'case'45'inr_232 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_232 = erased
-- Once.Arith.SigOp.Block.M.sem-cata
d_sem'45'cata_234 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'cata_234 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v0 v1 v3
-- Once.Arith.SigOp.Block.M.sem-cata-In-id
d_sem'45'cata'45'In'45'id_236 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_236 = erased
-- Once.Arith.SigOp.Block.M.sem-cata-compute
d_sem'45'cata'45'compute_238 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_238 = erased
-- Once.Arith.SigOp.Block.M.sem-fmap
d_sem'45'fmap_240 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_240 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 v0 v3 v4
-- Once.Arith.SigOp.Block.M.sem-fmap-Type
d_sem'45'fmap'45'Type_242 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_242 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_476 v0 v3
      v4
-- Once.Arith.SigOp.Block.M.sem-fst
d_sem'45'fst_244 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_244 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_308 v2
-- Once.Arith.SigOp.Block.M.sem-fst-pair
d_sem'45'fst'45'pair_246 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_246 = erased
-- Once.Arith.SigOp.Block.M.sem-functor-coherence
d_sem'45'functor'45'coherence_248 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_248 = erased
-- Once.Arith.SigOp.Block.M.sem-fuse
d_sem'45'fuse_250 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuse_250 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuse_1130 v0 v1 v2 v3 v5
      v6
-- Once.Arith.SigOp.Block.M.sem-fuseNat
d_sem'45'fuseNat_252 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuseNat_252 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1154 v0 v1 v2 v3
      v5 v6
-- Once.Arith.SigOp.Block.M.sem-hylo
d_sem'45'hylo_254 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'hylo_254 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'hylo_1176 v0 v1 v2 v3 v5
      v6
-- Once.Arith.SigOp.Block.M.sem-hylo-is-fuse
d_sem'45'hylo'45'is'45'fuse_256 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'hylo'45'is'45'fuse_256 = erased
-- Once.Arith.SigOp.Block.M.sem-inl
d_sem'45'inl_258 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_258 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_330
-- Once.Arith.SigOp.Block.M.sem-inr
d_sem'45'inr_260 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_260 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_336
-- Once.Arith.SigOp.Block.M.sem-pair
d_sem'45'pair_262 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_262 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320 v2 v3
-- Once.Arith.SigOp.Block.M.sem-para
d_sem'45'para_264 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'para_264 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_970 v0 v1 v3 v4
-- Once.Arith.SigOp.Block.M.sem-snd
d_sem'45'snd_266 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_266 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_314 v2
-- Once.Arith.SigOp.Block.M.sem-snd-pair
d_sem'45'snd'45'pair_268 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_268 = erased
-- Once.Arith.SigOp.Block.M.sfmap-bisim
d_sfmap'45'bisim_270 ::
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__688) ->
  AgdaAny -> AgdaAny
d_sfmap'45'bisim_270 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmap'45'bisim_1410 v0 v4 v5
-- Once.Arith.SigOp.Block.M.⟦_⟧
d_'10214'_'10215'_272 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_272 = erased
-- Once.Arith.SigOp.Block.M.⟦_⟧F
d_'10214'_'10215'F_274 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_274 = erased
-- Once.Arith.SigOp.Block.M.⟦μ⟧
d_'10214'μ'10215'_276 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'μ'10215'_276 = erased
-- Once.Arith.SigOp.Block.M.⟦ν⟧
d_'10214'ν'10215'_278 :: MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'ν'10215'_278 = erased
-- Once.Arith.SigOp.Block.show-side
d_show'45'side_280 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'side_280 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_Fst_24
        -> coe ("F" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_Snd_26
        -> coe ("S" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-path
d_show'45'path_282 ::
  [MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'path_282 v0
  = case coe v0 of
      [] -> coe ("Z" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_show'45'side_280 (coe v1)) (d_show'45'path_282 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-zlit
d_show'45'zlit_288 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'zlit_288 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
            ("_" :: Data.Text.Text)
      _ -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("n" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (subInt (coe (0 :: Integer)) (coe v0)))
                ("_" :: Data.Text.Text))
-- Once.Arith.SigOp.Block.show-arith-ir
d_show'45'arith'45'ir_296 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'arith'45'ir_296 ~v0 v1 = du_show'45'arith'45'ir_296 v1
du_show'45'arith'45'ir_296 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_show'45'arith'45'ir_296 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("L" :: Data.Text.Text) (d_show'45'zlit_288 (coe v1))
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("I" :: Data.Text.Text) (d_show'45'path_282 (coe v1))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("A" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_296 (coe v1))
                (coe du_show'45'arith'45'ir_296 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("B" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_296 (coe v1))
                (coe du_show'45'arith'45'ir_296 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("M" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_296 (coe v1))
                (coe du_show'45'arith'45'ir_296 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_24 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("G" :: Data.Text.Text) (coe du_show'45'arith'45'ir_296 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-digest
d_block'45'digest_318 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'digest_318 ~v0 v1 = du_block'45'digest_318 v1
du_block'45'digest_318 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_block'45'digest_318 v0 = coe du_show'45'arith'45'ir_296 (coe v0)
-- Once.Arith.SigOp.Block.block-name
d_block'45'name_324 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'name_324 ~v0 v1 = du_block'45'name_324 v1
du_block'45'name_324 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_block'45'name_324 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("arith.block." :: Data.Text.Text)
      (coe du_block'45'digest_318 (coe v0))
-- Once.Arith.SigOp.Block.toShape-I
d_toShape'45'I_330 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  AgdaAny -> AgdaAny
d_toShape'45'I_330 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_shape'45'unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_shape'45'int_12
        -> coe v1
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_shape'45'pair_14 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_toShape'45'I_330 (coe v2) (coe v4))
                    (coe d_toShape'45'I_330 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.projectM
d_projectM_348 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22] ->
  AgdaAny -> Maybe Integer
d_projectM_348 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_shape'45'unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_shape'45'int_12
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             (:) v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsState.C_shape'45'pair_14 v3 v4
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Arith.Machine.AbsState.C_Fst_24
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_projectM_348 (coe v3) (coe v6) (coe v7)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Arith.Machine.AbsState.C_Snd_26
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_projectM_348 (coe v4) (coe v6) (coe v8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.maybe-zeroM
d_maybe'45'zeroM_364 :: Maybe Integer -> Integer
d_maybe'45'zeroM_364 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-semM
d_block'45'semM_370 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_block'45'semM_370 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v3
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_18 (coe (64 :: Integer)) (coe v3)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v3
        -> coe
             d_maybe'45'zeroM_364
             (coe d_projectM_348 (coe v0) (coe v3) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__24 (coe (64 :: Integer))
             (coe d_block'45'semM_370 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_370 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__30 (coe (64 :: Integer))
             (coe d_block'45'semM_370 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_370 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__36 (coe (64 :: Integer))
             (coe d_block'45'semM_370 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_370 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_24 v3
        -> coe
             MAlonzo.Code.Once.Word.d_'8861'__42 (coe (64 :: Integer))
             (coe d_block'45'semM_370 (coe v0) (coe v3) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-info
d_block'45'info_404 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_264
d_block'45'info_404 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_282
      (coe du_block'45'name_324 (coe v1))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.Arith.Machine.IR.d_eval'45'arith_28
              (coe v0) (coe v1) (coe d_toShape'45'I_330 (coe v0) (coe v2))))
      (coe d_block'45'semM_370 (coe v0) (coe v1))
