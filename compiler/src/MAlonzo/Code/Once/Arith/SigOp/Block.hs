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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.SigOp.Block.W._%ˢ_
d__'37''738'__10 :: Integer -> Integer -> Integer
d__'37''738'__10
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__102 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._/ˢ_
d__'47''738'__12 :: Integer -> Integer -> Integer
d__'47''738'__12
  = coe MAlonzo.Code.Once.Word.d__'47''738'__96 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._<ˢ_
d__'60''738'__14 :: Integer -> Integer -> Bool
d__'60''738'__14
  = coe MAlonzo.Code.Once.Word.d__'60''738'__56 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._≡ʷ_
d__'8801''695'__16 :: Integer -> Integer -> Bool
d__'8801''695'__16 = coe MAlonzo.Code.Once.Word.du__'8801''695'__62
-- Once.Arith.SigOp.Block.W._⊕_
d__'8853'__18 :: Integer -> Integer -> Integer
d__'8853'__18
  = coe MAlonzo.Code.Once.Word.d__'8853'__24 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._⊖_
d__'8854'__20 :: Integer -> Integer -> Integer
d__'8854'__20
  = coe MAlonzo.Code.Once.Word.d__'8854'__30 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W._⊗_
d__'8855'__22 :: Integer -> Integer -> Integer
d__'8855'__22
  = coe MAlonzo.Code.Once.Word.d__'8855'__36 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.Word
d_Word_24 :: ()
d_Word_24 = erased
-- Once.Arith.SigOp.Block.W.fromℤ
d_fromℤ_26 :: Integer -> Integer
d_fromℤ_26
  = coe MAlonzo.Code.Once.Word.d_fromℤ_18 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.half
d_half_28 :: Integer
d_half_28
  = coe MAlonzo.Code.Once.Word.d_half_46 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.intMin
d_intMin_30 :: Integer
d_intMin_30
  = coe MAlonzo.Code.Once.Word.d_intMin_52 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.modulus
d_modulus_32 :: Integer
d_modulus_32
  = coe MAlonzo.Code.Once.Word.d_modulus_8 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.modulus≢0
d_modulus'8802'0_34 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_34
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_10 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.negOne
d_negOne_36 :: Integer
d_negOne_36
  = coe MAlonzo.Code.Once.Word.d_negOne_54 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.norm
d_norm_38 :: Integer -> Integer
d_norm_38
  = coe MAlonzo.Code.Once.Word.d_norm_14 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.toℤ
d_toℤ_40 :: Integer -> Integer
d_toℤ_40
  = coe MAlonzo.Code.Once.Word.d_toℤ_48 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.W.⊝_
d_'8861'__42 :: Integer -> Integer
d_'8861'__42
  = coe MAlonzo.Code.Once.Word.d_'8861'__42 (coe (64 :: Integer))
-- Once.Arith.SigOp.Block.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_46 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_46
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'base'45'to'45'full_648
-- Once.Arith.SigOp.Block.M.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_48 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_48 = erased
-- Once.Arith.SigOp.Block.M.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_50 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_50 = erased
-- Once.Arith.SigOp.Block.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_52 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_52
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'full'45'to'45'base_612
-- Once.Arith.SigOp.Block.M.coerce-functor
d_coerce'45'functor_54 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_54 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 v0 v2
-- Once.Arith.SigOp.Block.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_56 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_56 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      v0 v2
-- Once.Arith.SigOp.Block.M.coerce-round-trip
d_coerce'45'round'45'trip_58 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_58 = erased
-- Once.Arith.SigOp.Block.M.coerce-struct
d_coerce'45'struct_60 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_60
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct_280
-- Once.Arith.SigOp.Block.M.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_62 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_62 = erased
-- Once.Arith.SigOp.Block.M.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_64 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_64
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'struct'8315''185'_286
-- Once.Arith.SigOp.Block.M.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_66 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_66 = erased
-- Once.Arith.SigOp.Block.M.coerce-μ-in
d_coerce'45'μ'45'in_68 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_68 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'in_760 v0 v2
-- Once.Arith.SigOp.Block.M.coerce-μ-out
d_coerce'45'μ'45'out_70 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_70 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'μ'45'out_802 v0 v1 v3
-- Once.Arith.SigOp.Block.M.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_72 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_72 = erased
-- Once.Arith.SigOp.Block.M.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_74 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_74 = erased
-- Once.Arith.SigOp.Block.M.coerce-ν-in
d_coerce'45'ν'45'in_76 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_76
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'in_994
-- Once.Arith.SigOp.Block.M.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_78 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_78 = erased
-- Once.Arith.SigOp.Block.M.coerce-ν-out
d_coerce'45'ν'45'out_80 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_80
  = coe MAlonzo.Code.Once.Semantics.Core.du_coerce'45'ν'45'out_1000
-- Once.Arith.SigOp.Block.M.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_82 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_82 = erased
-- Once.Arith.SigOp.Block.M.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_84 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_84 = erased
-- Once.Arith.SigOp.Block.M.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_86 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_86 = erased
-- Once.Arith.SigOp.Block.M.fmap-struct-coherence
d_fmap'45'struct'45'coherence_88 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_88 = erased
-- Once.Arith.SigOp.Block.M.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_90 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_90 = erased
-- Once.Arith.SigOp.Block.M.funext
d_funext_92 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funext_92 = erased
-- Once.Arith.SigOp.Block.M.sem-CoIn
d_sem'45'CoIn_94 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'CoIn_94
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoIn_1014
-- Once.Arith.SigOp.Block.M.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_96 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_96 = erased
-- Once.Arith.SigOp.Block.M.sem-CoOut
d_sem'45'CoOut_98 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
d_sem'45'CoOut_98
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'CoOut_1004
-- Once.Arith.SigOp.Block.M.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_100 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_100 = erased
-- Once.Arith.SigOp.Block.M.sem-In
d_sem'45'In_102 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
d_sem'45'In_102
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'In_934
-- Once.Arith.SigOp.Block.M.sem-In-Out
d_sem'45'In'45'Out_104 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_104 = erased
-- Once.Arith.SigOp.Block.M.sem-Out
d_sem'45'Out_106 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'Out_106
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'Out_942
-- Once.Arith.SigOp.Block.M.sem-Out-In
d_sem'45'Out'45'In_108 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_108 = erased
-- Once.Arith.SigOp.Block.M.sem-ana
d_sem'45'ana_110 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'ana_110 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114 v0 v2 v3
-- Once.Arith.SigOp.Block.M.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_112 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_112 = erased
-- Once.Arith.SigOp.Block.M.sem-ana-bisim-anaS
d_sem'45'ana'45'bisim'45'anaS_114 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__738
d_sem'45'ana'45'bisim'45'anaS_114 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana'45'bisim'45'anaS_1548
      v0 v2
-- Once.Arith.SigOp.Block.M.sem-ana-is-anaS-unfoldS
d_sem'45'ana'45'is'45'anaS'45'unfoldS_116 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'is'45'anaS'45'unfoldS_116 = erased
-- Once.Arith.SigOp.Block.M.sem-case
d_sem'45'case_118 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_118 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'case_344 v3 v4 v5
-- Once.Arith.SigOp.Block.M.sem-case-inl
d_sem'45'case'45'inl_120 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_120 = erased
-- Once.Arith.SigOp.Block.M.sem-case-inr
d_sem'45'case'45'inr_122 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_122 = erased
-- Once.Arith.SigOp.Block.M.sem-cata
d_sem'45'cata_124 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'cata_124 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v0 v1 v3
-- Once.Arith.SigOp.Block.M.sem-cata-In-id
d_sem'45'cata'45'In'45'id_126 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_126 = erased
-- Once.Arith.SigOp.Block.M.sem-cata-compute
d_sem'45'cata'45'compute_128 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_128 = erased
-- Once.Arith.SigOp.Block.M.sem-fmap
d_sem'45'fmap_130 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_130 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 v0 v3 v4
-- Once.Arith.SigOp.Block.M.sem-fmap-Type
d_sem'45'fmap'45'Type_132 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_132 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap'45'Type_476 v0 v3
      v4
-- Once.Arith.SigOp.Block.M.sem-fst
d_sem'45'fst_134 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_134 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'fst_308 v2
-- Once.Arith.SigOp.Block.M.sem-fst-pair
d_sem'45'fst'45'pair_136 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_136 = erased
-- Once.Arith.SigOp.Block.M.sem-functor-coherence
d_sem'45'functor'45'coherence_138 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_138 = erased
-- Once.Arith.SigOp.Block.M.sem-fuse
d_sem'45'fuse_140 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuse_140 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuse_1130 v0 v1 v2 v3 v5
      v6
-- Once.Arith.SigOp.Block.M.sem-fuse-events
d_sem'45'fuse'45'events_142 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuse'45'events_142 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuse'45'events_1204 v1
      v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.Block.M.sem-fuseNat
d_sem'45'fuseNat_144 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuseNat_144 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat_1154 v0 v1 v2 v3
      v5 v6
-- Once.Arith.SigOp.Block.M.sem-hylo
d_sem'45'hylo_146 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'hylo_146 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'hylo_1176 v0 v1 v2 v3 v5
      v6
-- Once.Arith.SigOp.Block.M.sem-hylo-events
d_sem'45'hylo'45'events_148 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'hylo'45'events_148 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'hylo'45'events_1244 v1
      v2 v3 v4 v5 v6 v8 v9
-- Once.Arith.SigOp.Block.M.sem-hylo-is-fuse
d_sem'45'hylo'45'is'45'fuse_150 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'hylo'45'is'45'fuse_150 = erased
-- Once.Arith.SigOp.Block.M.sem-inl
d_sem'45'inl_152 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_152 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inl_330
-- Once.Arith.SigOp.Block.M.sem-inr
d_sem'45'inr_154 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_154 v0 v1
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'inr_336
-- Once.Arith.SigOp.Block.M.sem-pair
d_sem'45'pair_156 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_156 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'pair_320 v2 v3
-- Once.Arith.SigOp.Block.M.sem-para
d_sem'45'para_158 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'para_158 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_970 v0 v1 v3 v4
-- Once.Arith.SigOp.Block.M.sem-snd
d_sem'45'snd_160 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_160 v0 v1 v2
  = coe MAlonzo.Code.Once.Semantics.Core.du_sem'45'snd_314 v2
-- Once.Arith.SigOp.Block.M.sem-snd-pair
d_sem'45'snd'45'pair_162 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_162 = erased
-- Once.Arith.SigOp.Block.M.sfmap-bisim
d_sfmap'45'bisim_164 ::
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__738) ->
  AgdaAny -> AgdaAny
d_sfmap'45'bisim_164 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_sfmap'45'bisim_1486 v0 v4 v5
-- Once.Arith.SigOp.Block.M.⟦_⟧
d_'10214'_'10215'_166 :: MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_166 = erased
-- Once.Arith.SigOp.Block.M.⟦_⟧F
d_'10214'_'10215'F_168 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_168 = erased
-- Once.Arith.SigOp.Block.M.⟦μ⟧
d_'10214'μ'10215'_170 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_170 = erased
-- Once.Arith.SigOp.Block.M.⟦ν⟧
d_'10214'ν'10215'_172 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_172 = erased
-- Once.Arith.SigOp.Block.show-side
d_show'45'side_174 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'side_174 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
        -> coe ("F" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
        -> coe ("S" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-path
d_show'45'path_176 ::
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'path_176 v0
  = case coe v0 of
      [] -> coe ("Z" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_show'45'side_174 (coe v1)) (d_show'45'path_176 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-zlit
d_show'45'zlit_182 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'zlit_182 v0
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
d_show'45'arith'45'ir_190 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'arith'45'ir_190 ~v0 v1 = du_show'45'arith'45'ir_190 v1
du_show'45'arith'45'ir_190 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_show'45'arith'45'ir_190 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("L" :: Data.Text.Text) (d_show'45'zlit_182 (coe v1))
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("I" :: Data.Text.Text) (d_show'45'path_176 (coe v1))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("A" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_190 (coe v1))
                (coe du_show'45'arith'45'ir_190 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("B" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_190 (coe v1))
                (coe du_show'45'arith'45'ir_190 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("M" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_190 (coe v1))
                (coe du_show'45'arith'45'ir_190 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_24 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("G" :: Data.Text.Text) (coe du_show'45'arith'45'ir_190 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-digest
d_block'45'digest_212 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'digest_212 ~v0 v1 = du_block'45'digest_212 v1
du_block'45'digest_212 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_block'45'digest_212 v0 = coe du_show'45'arith'45'ir_190 (coe v0)
-- Once.Arith.SigOp.Block.block-name
d_block'45'name_218 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'name_218 ~v0 v1 = du_block'45'name_218 v1
du_block'45'name_218 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_block'45'name_218 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("arith.block." :: Data.Text.Text)
      (coe du_block'45'digest_212 (coe v0))
-- Once.Arith.SigOp.Block.projectM
d_projectM_224 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  AgdaAny -> Maybe Integer
d_projectM_224 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             (:) v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_14 v3 v4
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_projectM_224 (coe v3) (coe v6) (coe v7)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_projectM_224 (coe v4) (coe v6) (coe v8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.maybe-zeroM
d_maybe'45'zeroM_240 :: Maybe Integer -> Integer
d_maybe'45'zeroM_240 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-semM
d_block'45'semM_246 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_block'45'semM_246 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v3
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_18 (coe (64 :: Integer)) (coe v3)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v3
        -> coe
             d_maybe'45'zeroM_240
             (coe d_projectM_224 (coe v0) (coe v3) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__24 (coe (64 :: Integer))
             (coe d_block'45'semM_246 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_246 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__30 (coe (64 :: Integer))
             (coe d_block'45'semM_246 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_246 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v3 v4
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__36 (coe (64 :: Integer))
             (coe d_block'45'semM_246 (coe v0) (coe v3) (coe v2))
             (coe d_block'45'semM_246 (coe v0) (coe v4) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_24 v3
        -> coe
             MAlonzo.Code.Once.Word.d_'8861'__42 (coe (64 :: Integer))
             (coe d_block'45'semM_246 (coe v0) (coe v3) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-info
d_block'45'info_280 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154
d_block'45'info_280 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_172
      (coe du_block'45'name_218 (coe v1))
      (coe d_block'45'semM_246 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_144)
