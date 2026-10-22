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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Primitives where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._%ˢ_
d__'37''738'__14 :: Integer -> Integer -> Integer
d__'37''738'__14
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._/ˢ_
d__'47''738'__16 :: Integer -> Integer -> Integer
d__'47''738'__16
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._<ˢ_
d__'60''738'__18 :: Integer -> Integer -> Bool
d__'60''738'__18
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._divℕ_
d__divℕ__20 :: Integer -> Integer -> Integer
d__divℕ__20 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._modℕ_
d__modℕ__22 :: Integer -> Integer -> Integer
d__modℕ__22 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._≡ʷ_
d__'8801''695'__24 :: Integer -> Integer -> Bool
d__'8801''695'__24
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._⊕_
d__'8853'__26 :: Integer -> Integer -> Integer
d__'8853'__26
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._⊖_
d__'8854'__28 :: Integer -> Integer -> Integer
d__'8854'__28
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW._⊗_
d__'8855'__30 :: Integer -> Integer -> Integer
d__'8855'__30
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.InRange
d_InRange_32 :: Integer -> ()
d_InRange_32 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.Word
d_Word_34 :: ()
d_Word_34 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.fromℤ
d_fromℤ_36 :: Integer -> Integer
d_fromℤ_36
  = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.half
d_half_38 :: Integer
d_half_38
  = coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.inRange?
d_inRange'63'_40 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_40
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.intMin
d_intMin_42 :: Integer
d_intMin_42
  = coe MAlonzo.Code.Once.Spec.Word.d_intMin_56 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.modulus
d_modulus_44 :: Integer
d_modulus_44
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.modulus≢0
d_modulus'8802'0_46 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_46
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.negOne
d_negOne_48 :: Integer
d_negOne_48
  = coe MAlonzo.Code.Once.Spec.Word.d_negOne_58 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.norm
d_norm_50 :: Integer -> Integer
d_norm_50
  = coe MAlonzo.Code.Once.Spec.Word.d_norm_18 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.tdivℤ
d_tdivℤ_52 :: Integer -> Integer -> Integer
d_tdivℤ_52 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.tmodℤ
d_tmodℤ_54 :: Integer -> Integer -> Integer
d_tmodℤ_54 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.toWord
d_toWord_56 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_56 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72 (coe (64 :: Integer)) v0
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.toℤ
d_toℤ_58 :: Integer -> Integer
d_toℤ_58
  = coe MAlonzo.Code.Once.Spec.Word.d_toℤ_52 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.IntW.⊝_
d_'8861'__60 :: Integer -> Integer
d_'8861'__60
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46 (coe (64 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp
d_compile'45'sigOp_62 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30]
d_compile'45'sigOp_62 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_54
         (coe
            MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
            (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp-size
d_compile'45'sigOp'45'size_66 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> Integer
d_compile'45'sigOp'45'size_66 ~v0 = du_compile'45'sigOp'45'size_66
du_compile'45'sigOp'45'size_66 :: Integer
du_compile'45'sigOp'45'size_66 = coe (1 :: Integer)
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp-length
d_compile'45'sigOp'45'length_70 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'sigOp'45'length_70 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const
d_compile'45'const_76 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30]
d_compile'45'const_76 ~v0 v1 v2 = du_compile'45'const_76 v1 v2
du_compile'45'const_76 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30]
du_compile'45'const_76 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_fits'45'int_26
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                   (coe
                      MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (64 :: Integer))
                      (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Type.C_fits'45'float_28
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_32
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_24
                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_28
                   (coe
                      MAlonzo.Code.Once.Spec.Float.Decimal.d_round_176
                      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_44) (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const-size
d_compile'45'const'45'size_84 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 -> Integer
d_compile'45'const'45'size_84 ~v0 v1
  = du_compile'45'const'45'size_84 v1
du_compile'45'const'45'size_84 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_24 -> Integer
du_compile'45'const'45'size_84 v0
  = coe seq (coe v0) (coe (1 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const-length
d_compile'45'const'45'length_92 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'const'45'length_92 = erased
