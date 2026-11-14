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

module MAlonzo.Code.Once.Arith.SigOp.Builders where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.IR.Semantics.Polynomial
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Type.Core
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.SigOp.Builders.W._%ˢ_
d__'37''738'__12 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'37''738'__12 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._/ˢ_
d__'47''738'__14 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'47''738'__14 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._<ˢ_
d__'60''738'__16 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'60''738'__16 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._divℕ_
d__divℕ__18 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__divℕ__18 ~v0 = du__divℕ__18
du__divℕ__18 :: Integer -> Integer -> Integer
du__divℕ__18 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.Arith.SigOp.Builders.W._modℕ_
d__modℕ__20 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__modℕ__20 ~v0 = du__modℕ__20
du__modℕ__20 :: Integer -> Integer -> Integer
du__modℕ__20 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.Arith.SigOp.Builders.W._≡ʷ_
d__'8801''695'__22 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'8801''695'__22 ~v0 = du__'8801''695'__22
du__'8801''695'__22 :: Integer -> Integer -> Bool
du__'8801''695'__22
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.Arith.SigOp.Builders.W._⊕_
d__'8853'__24 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8853'__24 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._⊖_
d__'8854'__26 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8854'__26 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._⊗_
d__'8855'__28 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8855'__28 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.InRange
d_InRange_30 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> ()
d_InRange_30 = erased
-- Once.Arith.SigOp.Builders.W.Word
d_Word_32 :: MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> ()
d_Word_32 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ
d_fromℤ_34 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_fromℤ_34 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.half
d_half_36 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_half_36 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_half_50
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.inRange?
d_inRange'63'_38 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_38 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.intMin
d_intMin_40 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_intMin_40 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_intMin_56
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.modulus
d_modulus_42 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_modulus_42 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.modulus≢0
d_modulus'8802'0_44 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_44 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.negOne
d_negOne_46 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_negOne_46 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_negOne_58
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.norm
d_norm_48 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_norm_48 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_norm_18
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.tdivℤ
d_tdivℤ_50 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tdivℤ_50 ~v0 = du_tdivℤ_50
du_tdivℤ_50 :: Integer -> Integer -> Integer
du_tdivℤ_50 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.Arith.SigOp.Builders.W.tmodℤ
d_tmodℤ_52 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tmodℤ_52 ~v0 = du_tmodℤ_52
du_tmodℤ_52 :: Integer -> Integer -> Integer
du_tmodℤ_52 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.Arith.SigOp.Builders.W.toWord
d_toWord_54 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_54 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)) v1
-- Once.Arith.SigOp.Builders.W.toℤ
d_toℤ_56 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_toℤ_56 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_toℤ_52
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.⊝_
d_'8861'__58 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_'8861'__58 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_62 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_62 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'base'45'to'45'full_422
      v2 v3 v4
-- Once.Arith.SigOp.Builders.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_64 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_64 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'full'45'to'45'base_386
      v1 v2
-- Once.Arith.SigOp.Builders.M.coerce-functor
d_coerce'45'functor_66 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_66 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor_254 v1 v3
-- Once.Arith.SigOp.Builders.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_68 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_68 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor'8315''185'_298
      v1 v3
-- Once.Arith.SigOp.Builders.M.coerce-μ-in
d_coerce'45'μ'45'in_70 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_70 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'in_456 v1 v3
-- Once.Arith.SigOp.Builders.M.coerce-μ-out
d_coerce'45'μ'45'out_72 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_72 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'out_502 v2
      v3 v5
-- Once.Arith.SigOp.Builders.M.coerce-ν-in
d_coerce'45'ν'45'in_74 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_74 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618
-- Once.Arith.SigOp.Builders.M.coerce-ν-out
d_coerce'45'ν'45'out_76 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_76 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'out_628 v2
-- Once.Arith.SigOp.Builders.M.eraseᵍ
d_erase'7501'_78 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_78 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112 v1 v2
-- Once.Arith.SigOp.Builders.M.sem-CoIn
d_sem'45'CoIn_80 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'CoIn_80 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoIn_648 v1 v2
-- Once.Arith.SigOp.Builders.M.sem-CoOut
d_sem'45'CoOut_82 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_82 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoOut_636 v2 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-In
d_sem'45'In_84 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_84 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'In_544 v1 v2
-- Once.Arith.SigOp.Builders.M.sem-Out
d_sem'45'Out_86 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_86 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'Out_556 v2 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-ana
d_sem'45'ana_88 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'ana_88 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'ana_660 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-cata
d_sem'45'cata_90 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_90 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'cata_572 v2 v3 v5
-- Once.Arith.SigOp.Builders.M.sem-fmap
d_sem'45'fmap_92 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_92 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'fmap_344 v1 v4 v5
-- Once.Arith.SigOp.Builders.M.sem-para
d_sem'45'para_94 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_94 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'para_592 v2 v3 v5 v6
-- Once.Arith.SigOp.Builders.M.semAnaLayer
d_semAnaLayer_96 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_96 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_semAnaLayer_668 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.sfmapSemAna
d_sfmapSemAna_98 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_98 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sfmapSemAna_678 v0 v1 v2 v4
      v5
-- Once.Arith.SigOp.Builders.M.⟦_⟧
d_'10214'_'10215'_100 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_100 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧F
d_'10214'_'10215'F_102 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_102 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_104 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_104 = erased
-- Once.Arith.SigOp.Builders.M.⟦μ⟧
d_'10214'μ'10215'_106 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_106 = erased
-- Once.Arith.SigOp.Builders.M.⟦ν⟧
d_'10214'ν'10215'_108 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_108 = erased
-- Once.Arith.SigOp.Builders.base-I×I
d_base'45'I'215'I_110 :: MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'45'I'215'I_110
  = coe
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
-- Once.Arith.SigOp.Builders.base-U+U
d_base'45'U'43'U_112 :: MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'45'U'43'U_112
  = coe
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
-- Once.Arith.SigOp.Builders.add-info
d_add'45'info_114 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_add'45'info_114
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.add.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'add_230))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
-- Once.Arith.SigOp.Builders.sub-info
d_sub'45'info_116 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_sub'45'info_116
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.sub.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'sub_232))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
-- Once.Arith.SigOp.Builders.mul-info
d_mul'45'info_118 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_mul'45'info_118
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.mul.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'mul_234))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
-- Once.Arith.SigOp.Builders.div-info
d_div'45'info_120 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_div'45'info_120
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.div.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'div_236))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
-- Once.Arith.SigOp.Builders.mod-info
d_mod'45'info_122 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_mod'45'info_122
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.mod.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'mod_238))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
-- Once.Arith.SigOp.Builders.neg-info
d_neg'45'info_124 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_neg'45'info_124
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.neg.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_240))
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
-- Once.Arith.SigOp.Builders.base-F×F
d_base'45'F'215'F_126 :: MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'45'F'215'F_126
  = coe
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100)
-- Once.Arith.SigOp.Builders.fadd-info
d_fadd'45'info_128 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_fadd'45'info_128
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.add.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fadd_242))
      (coe d_base'45'F'215'F_126)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100)
-- Once.Arith.SigOp.Builders.fsub-info
d_fsub'45'info_130 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_fsub'45'info_130
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.sub.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fsub_244))
      (coe d_base'45'F'215'F_126)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100)
-- Once.Arith.SigOp.Builders.fmul-info
d_fmul'45'info_132 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_fmul'45'info_132
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.mul.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fmul_246))
      (coe d_base'45'F'215'F_126)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100)
-- Once.Arith.SigOp.Builders.fdiv-info
d_fdiv'45'info_134 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_fdiv'45'info_134
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.div.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fdiv_248))
      (coe d_base'45'F'215'F_126)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100)
-- Once.Arith.SigOp.Builders.i2f-info
d_i2f'45'info_136 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_i2f'45'info_136
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.i2f" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'i2f_250))
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100)
-- Once.Arith.SigOp.Builders.numPrim
d_numPrim_144 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Theory_16 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_228
d_numPrim_144 ~v0 ~v1 ~v2 v3 v4 = du_numPrim_144 v3 v4
du_numPrim_144 ::
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_228
du_numPrim_144 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Theory.C_int'45'neg_106
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_240)
      MAlonzo.Code.Once.Spec.Theory.C_int'45'ring_108
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_'8245''43'_42
               -> coe MAlonzo.Code.Once.Arith.Prim.C_p'45'add_230
             MAlonzo.Code.Once.Spec.Theory.C_'8245''45'_44
               -> coe MAlonzo.Code.Once.Arith.Prim.C_p'45'sub_232
             MAlonzo.Code.Once.Spec.Theory.C_'8245''42'_46
               -> coe MAlonzo.Code.Once.Arith.Prim.C_p'45'mul_234
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Theory.C_int'45'division_110
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_'8245''47'_48
               -> coe MAlonzo.Code.Once.Arith.Prim.C_p'45'div_236
             MAlonzo.Code.Once.Spec.Theory.C_'8245''37'_50
               -> coe MAlonzo.Code.Once.Arith.Prim.C_p'45'mod_238
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Theory.C_int'45'order_112
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_'8245''60'_52
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
                    (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'lt_8)
             MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61'_54
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
                    (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'le_10)
             MAlonzo.Code.Once.Spec.Theory.C_'8245''62'_56
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
                    (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'gt_12)
             MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61'_58
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
                    (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ge_14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Theory.C_int'45'equality_114
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61'_60
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
                    (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'eq_16)
             MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61'_62
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
                    (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ne_18)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Theory.C_float'45'neg_116
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fneg_252)
      MAlonzo.Code.Once.Spec.Theory.C_float'45'rounded_118
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_'8245''43''7496'_64
               -> coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fadd_242
             MAlonzo.Code.Once.Spec.Theory.C_'8245''45''7496'_66
               -> coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fsub_244
             MAlonzo.Code.Once.Spec.Theory.C_'8245''42''7496'_68
               -> coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fmul_246
             MAlonzo.Code.Once.Spec.Theory.C_'8245''47''7496'_70
               -> coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fdiv_248
             MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61''7496'_72
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28) (coe v0) (coe v1)
             MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61''7496'_74
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28) (coe v0) (coe v1)
             MAlonzo.Code.Once.Spec.Theory.C_'8245''60''7496'_76
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28) (coe v0) (coe v1)
             MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61''7496'_78
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28) (coe v0) (coe v1)
             MAlonzo.Code.Once.Spec.Theory.C_'8245''62''7496'_80
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28) (coe v0) (coe v1)
             MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61''7496'_82
               -> coe
                    MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256
                    (coe MAlonzo.Code.Once.Spec.Theory.C_Rounded_28) (coe v0) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Theory.C_float'45'order_120
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256
                (coe MAlonzo.Code.Once.Spec.Theory.C_Order_24) (coe v0) (coe v1))
      MAlonzo.Code.Once.Spec.Theory.C_float'45'equality_122
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Once.Arith.Prim.C_p'45'fcmp_256
                (coe MAlonzo.Code.Once.Spec.Theory.C_Equality_26) (coe v0)
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.symText
d_symText_150 ::
  MAlonzo.Code.Once.Spec.Theory.T_Theory_16 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_symText_150 ~v0 ~v1 v2 = du_symText_150 v2
du_symText_150 ::
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_symText_150 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Theory.C_'8245'neg_40
        -> coe ("neg" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''43'_42
        -> coe ("add" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''45'_44
        -> coe ("sub" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''42'_46
        -> coe ("mul" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''47'_48
        -> coe ("div" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''37'_50
        -> coe ("mod" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''60'_52
        -> coe ("lt" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61'_54
        -> coe ("le" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''62'_56
        -> coe ("gt" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61'_58
        -> coe ("ge" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61'_60
        -> coe ("eq" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61'_62
        -> coe ("ne" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''43''7496'_64
        -> coe ("add" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''45''7496'_66
        -> coe ("sub" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''42''7496'_68
        -> coe ("mul" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''47''7496'_70
        -> coe ("div" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61''7496'_72
        -> coe ("eq.ieee" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61''7496'_74
        -> coe ("ne.ieee" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''60''7496'_76
        -> coe ("lt.ieee" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61''7496'_78
        -> coe ("le.ieee" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''62''7496'_80
        -> coe ("gt.ieee" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61''7496'_82
        -> coe ("ge.ieee" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.numTyText
d_numTyText_152 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_numTyText_152 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Theory.C_int_8
        -> coe ("int" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Theory.C_float_10
        -> coe ("float" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.numName
d_numName_160 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Theory_16 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_numName_160 v0 ~v1 ~v2 ~v3 v4 = du_numName_160 v0 v4
du_numName_160 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_numName_160 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("arith." :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe du_symText_150 (coe v1))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("." :: Data.Text.Text) (d_numTyText_152 (coe v0))))
-- Once.Arith.SigOp.Builders.symBaseDom
d_symBaseDom_172 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_symBaseDom_172 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Theory.C_int_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_unary_32
               -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
             MAlonzo.Code.Once.Spec.Theory.C_binary_34
               -> coe d_base'45'I'215'I_110
             MAlonzo.Code.Once.Spec.Theory.C_compare_36
               -> coe d_base'45'I'215'I_110
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Theory.C_float_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_unary_32
               -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
             MAlonzo.Code.Once.Spec.Theory.C_binary_34
               -> coe d_base'45'F'215'F_126
             MAlonzo.Code.Once.Spec.Theory.C_compare_36
               -> coe d_base'45'F'215'F_126
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.symBaseCod
d_symBaseCod_178 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_symBaseCod_178 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Theory.C_int_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_unary_32
               -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
             MAlonzo.Code.Once.Spec.Theory.C_binary_34
               -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
             MAlonzo.Code.Once.Spec.Theory.C_compare_36
               -> coe d_base'45'U'43'U_112
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Theory.C_float_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Theory.C_unary_32
               -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
             MAlonzo.Code.Once.Spec.Theory.C_binary_34
               -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
             MAlonzo.Code.Once.Spec.Theory.C_compare_36
               -> coe d_base'45'U'43'U_112
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.numInfo
d_numInfo_186 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Theory_16 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_numInfo_186 v0 ~v1 v2 v3 v4 = du_numInfo_186 v0 v2 v3 v4
du_numInfo_186 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_numInfo_186 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe du_numName_160 (coe v0) (coe v3)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe du_numPrim_144 (coe v2) (coe v3)))
      (coe d_symBaseDom_172 (coe v0) (coe v1))
      (coe d_symBaseCod_178 (coe v0) (coe v1))
-- Once.Arith.SigOp.Builders.lt-info
d_lt'45'info_196 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_lt'45'info_196
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.lt.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'lt_8)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.le-info
d_le'45'info_198 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_le'45'info_198
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.le.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'le_10)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.gt-info
d_gt'45'info_200 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_gt'45'info_200
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.gt.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'gt_12)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.ge-info
d_ge'45'info_202 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_ge'45'info_202
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.ge.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ge_14)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.eq-info
d_eq'45'info_204 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_eq'45'info_204
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.eq.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'eq_16)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.ne-info
d_ne'45'info_206 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_ne'45'info_206
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.ne.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_96
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_258
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ne_18)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.value-info
d_value'45'info_212 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_value'45'info_212 ~v0 ~v1 v2 v3 v4
  = du_value'45'info_212 v2 v3 v4
du_value'45'info_212 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_value'45'info_212 v0 v1 v2
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.C_ffiV_88) (coe v1) (coe v2)
-- Once.Arith.SigOp.Builders.generic-info
d_generic'45'info_224 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_generic'45'info_224 ~v0 ~v1 = du_generic'45'info_224
du_generic'45'info_224 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_generic'45'info_224 = coe du_value'45'info_212
-- Once.Arith.SigOp.Builders.arrow-sem-eff
d_arrow'45'sem'45'eff_230 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
d_arrow'45'sem'45'eff_230 ~v0 ~v1 v2 v3
  = du_arrow'45'sem'45'eff_230 v2 v3
du_arrow'45'sem'45'eff_230 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
du_arrow'45'sem'45'eff_230 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_94)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_92)
                              else coe
                                     seq (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.C_callsV_90)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.arrow-sem
d_arrow'45'sem_236 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
d_arrow'45'sem_236 ~v0 v1 v2 = du_arrow'45'sem_236 v1 v2
du_arrow'45'sem_236 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
du_arrow'45'sem_236 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_fin_42 v4
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                      -> coe MAlonzo.Code.Once.SigOp.Info.C_ffiV_88
                    MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                      -> coe
                           du_arrow'45'sem'45'eff_230
                           (coe MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58 (coe v0))
                           (coe MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64 (coe v0))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_eff_44
               -> coe
                    du_arrow'45'sem'45'eff_230
                    (coe MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58 (coe v0))
                    (coe MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64 (coe v0))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.arrow-info
d_arrow'45'info_246 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_arrow'45'info_246 ~v0 v1 v2 v3 v4 v5
  = du_arrow'45'info_246 v1 v2 v3 v4 v5
du_arrow'45'info_246 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_arrow'45'info_246 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124 (coe v2)
      (coe du_arrow'45'sem_236 (coe v0) (coe v1)) (coe v3) (coe v4)
