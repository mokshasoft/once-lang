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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.IR.Semantics.Polynomial
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Arith
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.SigOp.Block.W._%ˢ_
d__'37''738'__12 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'37''738'__12 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W._/ˢ_
d__'47''738'__14 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'47''738'__14 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W._<ˢ_
d__'60''738'__16 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'60''738'__16 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W._divℕ_
d__divℕ__18 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__divℕ__18 ~v0 = du__divℕ__18
du__divℕ__18 :: Integer -> Integer -> Integer
du__divℕ__18 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.Arith.SigOp.Block.W._modℕ_
d__modℕ__20 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__modℕ__20 ~v0 = du__modℕ__20
du__modℕ__20 :: Integer -> Integer -> Integer
du__modℕ__20 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.Arith.SigOp.Block.W._≡ʷ_
d__'8801''695'__22 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'8801''695'__22 ~v0 = du__'8801''695'__22
du__'8801''695'__22 :: Integer -> Integer -> Bool
du__'8801''695'__22
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.Arith.SigOp.Block.W._⊕_
d__'8853'__24 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8853'__24 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W._⊖_
d__'8854'__26 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8854'__26 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W._⊗_
d__'8855'__28 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8855'__28 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.InRange
d_InRange_30 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> ()
d_InRange_30 = erased
-- Once.Arith.SigOp.Block.W.Word
d_Word_32 :: MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> ()
d_Word_32 = erased
-- Once.Arith.SigOp.Block.W.fromℤ
d_fromℤ_34 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_fromℤ_34 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.half
d_half_36 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_half_36 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_half_50
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.inRange?
d_inRange'63'_38 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_38 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.intMin
d_intMin_40 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_intMin_40 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_intMin_56
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.modulus
d_modulus_42 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_modulus_42 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.modulus≢0
d_modulus'8802'0_44 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_44 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.negOne
d_negOne_46 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_negOne_46 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_negOne_58
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.norm
d_norm_48 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_norm_48 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_norm_18
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.tdivℤ
d_tdivℤ_50 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tdivℤ_50 ~v0 = du_tdivℤ_50
du_tdivℤ_50 :: Integer -> Integer -> Integer
du_tdivℤ_50 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.Arith.SigOp.Block.W.tmodℤ
d_tmodℤ_52 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tmodℤ_52 ~v0 = du_tmodℤ_52
du_tmodℤ_52 :: Integer -> Integer -> Integer
du_tmodℤ_52 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.Arith.SigOp.Block.W.toWord
d_toWord_54 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_54 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)) v1
-- Once.Arith.SigOp.Block.W.toℤ
d_toℤ_56 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_toℤ_56 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_toℤ_52
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.W.⊝_
d_'8861'__58 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_'8861'__58 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Block.M.coerce-base-to-full
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
-- Once.Arith.SigOp.Block.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_64 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_64 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'full'45'to'45'base_386
      v1 v2
-- Once.Arith.SigOp.Block.M.coerce-functor
d_coerce'45'functor_66 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_66 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor_254 v1 v3
-- Once.Arith.SigOp.Block.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_68 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_68 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor'8315''185'_298
      v1 v3
-- Once.Arith.SigOp.Block.M.coerce-μ-in
d_coerce'45'μ'45'in_70 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_70 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'in_456 v1 v3
-- Once.Arith.SigOp.Block.M.coerce-μ-out
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
-- Once.Arith.SigOp.Block.M.coerce-ν-in
d_coerce'45'ν'45'in_74 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_74 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618
-- Once.Arith.SigOp.Block.M.coerce-ν-out
d_coerce'45'ν'45'out_76 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_76 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'out_628 v2
-- Once.Arith.SigOp.Block.M.eraseᵍ
d_erase'7501'_78 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_78 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112 v1 v2
-- Once.Arith.SigOp.Block.M.sem-CoIn
d_sem'45'CoIn_80 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'CoIn_80 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoIn_648 v1 v2
-- Once.Arith.SigOp.Block.M.sem-CoOut
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
-- Once.Arith.SigOp.Block.M.sem-In
d_sem'45'In_84 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_84 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'In_544 v1 v2
-- Once.Arith.SigOp.Block.M.sem-Out
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
-- Once.Arith.SigOp.Block.M.sem-ana
d_sem'45'ana_88 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'ana_88 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'ana_660 v0 v1 v3 v4
-- Once.Arith.SigOp.Block.M.sem-cata
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
-- Once.Arith.SigOp.Block.M.sem-fmap
d_sem'45'fmap_92 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_92 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'fmap_344 v1 v4 v5
-- Once.Arith.SigOp.Block.M.sem-para
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
-- Once.Arith.SigOp.Block.M.semAnaLayer
d_semAnaLayer_96 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_96 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_semAnaLayer_668 v0 v1 v3 v4
-- Once.Arith.SigOp.Block.M.sfmapSemAna
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
-- Once.Arith.SigOp.Block.M.⟦_⟧
d_'10214'_'10215'_100 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_100 = erased
-- Once.Arith.SigOp.Block.M.⟦_⟧F
d_'10214'_'10215'F_102 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_102 = erased
-- Once.Arith.SigOp.Block.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_104 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_104 = erased
-- Once.Arith.SigOp.Block.M.⟦μ⟧
d_'10214'μ'10215'_106 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_106 = erased
-- Once.Arith.SigOp.Block.M.⟦ν⟧
d_'10214'ν'10215'_108 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_108 = erased
-- Once.Arith.SigOp.Block.show-side
d_show'45'side_110 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'side_110 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
        -> coe ("F" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
        -> coe ("S" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-path
d_show'45'path_112 ::
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'path_112 v0
  = case coe v0 of
      [] -> coe ("Z" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_show'45'side_110 (coe v1)) (d_show'45'path_112 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.show-zlit
d_show'45'zlit_118 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'zlit_118 v0
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
-- Once.Arith.SigOp.Block.show-dlit
d_show'45'dlit_124 ::
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'dlit_124 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_show'45'zlit_118
         (coe MAlonzo.Code.Once.Spec.Float.Decimal.d_sig_14 (coe v0)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe
            MAlonzo.Code.Data.Nat.Show.d_show_56
            (MAlonzo.Code.Once.Spec.Float.Decimal.d_exp10_16 (coe v0)))
         ("_" :: Data.Text.Text))
-- Once.Arith.SigOp.Block.show-arith-ir
d_show'45'arith'45'ir_132 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'arith'45'ir_132 v0 ~v1 v2
  = du_show'45'arith'45'ir_132 v0 v2
du_show'45'arith'45'ir_132 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_show'45'arith'45'ir_132 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("L" :: Data.Text.Text) (d_show'45'zlit_118 (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aflit_16 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("F" :: Data.Text.Text) (d_show'45'dlit_124 (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("I" :: Data.Text.Text)
             (d_show'45'path_112
                (coe
                   MAlonzo.Code.Once.Arith.Machine.Shape.du_'8970'_'8971''7486'_114
                   (coe v0) (coe v3)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("A" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v3))
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v4)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("B" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v3))
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v4)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("M" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v3))
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v4)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("D" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v3))
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v4)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("R" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v2))
                (coe du_show'45'arith'45'ir_132 (coe v0) (coe v3)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("G" :: Data.Text.Text)
             (coe du_show'45'arith'45'ir_132 (coe v0) (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("C" :: Data.Text.Text)
             (coe du_show'45'arith'45'ir_132 (coe v0) (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_acmp_46 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("K" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_show'45'cmp_174 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (coe du_show'45'arith'45'ir_132 (coe v0) (coe v3))
                   (coe du_show'45'arith'45'ir_132 (coe v0) (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block._.show-cmp
d_show'45'cmp_174 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'cmp_174 ~v0 ~v1 ~v2 ~v3 v4 = du_show'45'cmp_174 v4
du_show'45'cmp_174 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_show'45'cmp_174 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'lt_8
        -> coe ("0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'le_10
        -> coe ("1" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'gt_12
        -> coe ("2" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ge_14
        -> coe ("3" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'eq_16
        -> coe ("4" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ne_18
        -> coe ("5" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-digest
d_block'45'digest_180 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'digest_180 v0 ~v1 v2 = du_block'45'digest_180 v0 v2
du_block'45'digest_180 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_block'45'digest_180 v0 v1
  = coe du_show'45'arith'45'ir_132 (coe v0) (coe v1)
-- Once.Arith.SigOp.Block.block-name
d_block'45'name_188 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'name_188 v0 ~v1 v2 = du_block'45'name_188 v0 v2
du_block'45'name_188 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_block'45'name_188 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("arith.block." :: Data.Text.Text)
      (coe du_block'45'digest_180 (coe v0) (coe v1))
-- Once.Arith.SigOp.Block.projectM
d_projectM_194 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> Maybe Integer
d_projectM_194 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> case coe v0 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> case coe v2 of
                    [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                    (:) v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14
        -> case coe v0 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> case coe v2 of
                    [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                    (:) v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v4 v5
        -> case coe v2 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> coe d_projectM_194 (coe v0) (coe v4) (coe v7) (coe v8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> coe d_projectM_194 (coe v0) (coe v5) (coe v7) (coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.readLeafM
d_readLeafM_220 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> Integer
d_readLeafM_220 v0 ~v1 v2 v3 = du_readLeafM_220 v0 v2 v3
du_readLeafM_220 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> Integer
du_readLeafM_220 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70 -> coe v2
      MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72 -> coe v2
      MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe du_readLeafM_220 (coe v7) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe du_readLeafM_220 (coe v8) (coe v6) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.maybe-zeroM
d_maybe'45'zeroM_234 :: Maybe Integer -> Integer
d_maybe'45'zeroM_234 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-semM
d_block'45'semM_242 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> Integer
d_block'45'semM_242 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v5
        -> coe
             MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v3))
             (coe v5)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aflit_16 v5
        -> coe
             MAlonzo.Code.Once.Spec.Float.Decimal.d_round_176
             (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v3))
             (coe v5)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v6
        -> coe du_readLeafM_220 (coe v0) (coe v6) (coe v4)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Spec.Word.d__'8853'__28
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v7) (coe v3) (coe v4))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Arith.d_fadd_316
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v7) (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Spec.Word.d__'8854'__34
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v7) (coe v3) (coe v4))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Arith.d_fsub_318
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v7) (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Spec.Word.d__'8855'__40
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v7) (coe v3) (coe v4))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Arith.d_fmul_320
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v7) (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Spec.Word.d__'47''738'__116
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v7) (coe v3) (coe v4))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Arith.d_fdiv_322
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v7) (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'37''738'__122
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v3))
             (coe
                d_block'45'semM_242 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v5) (coe v3)
                (coe v4))
             (coe
                d_block'45'semM_242 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v3)
                (coe v4))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Spec.Word.d_'8861'__46
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Spec.Float.Arith.d_fneg_358
                    (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v3))
                    (coe
                       d_block'45'semM_242 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44 v5
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_i2f_364
             (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Word.d_toℤ_52
                (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v3))
                (coe
                   d_block'45'semM_242 (coe v0)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v5) (coe v3)
                   (coe v4)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_acmp_46 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Arith.CmpOp.d_cmp'45'bit_62
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v3))
             (coe v5)
             (coe
                d_block'45'semM_242 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v3)
                (coe v4))
             (coe
                d_block'45'semM_242 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v3)
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.shape-as-type-base
d_shape'45'as'45'type'45'base_362 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_shape'45'as'45'type'45'base_362 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106
             (d_shape'45'as'45'type'45'base_362 (coe v1))
             (d_shape'45'as'45'type'45'base_362 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.numtype-as-type-base
d_numtype'45'as'45'type'45'base_370 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_numtype'45'as'45'type'45'base_370 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Type.C_NInt_8
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
      MAlonzo.Code.Once.Arith.Type.C_NFloat_10
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Block.block-info
d_block'45'info_376 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_block'45'info_376 v0 v1 v2
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_300
         (coe
            MAlonzo.Code.Once.Spec.Name.d_bare_14
            (coe du_block'45'name_188 (coe v0) (coe v2)))
         (coe d_block'45'semM_242 (coe v0) (coe v1) (coe v2))
         (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_62)
         (coe d_shape'45'as'45'type'45'base_362 (coe v0))
         (coe d_numtype'45'as'45'type'45'base_370 (coe v1)))
