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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimCore where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Backend.Correct
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.AbsInstr
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.Compile
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Word

-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.exec-xinstr
d_exec'45'xinstr_14 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_exec'45'xinstr_14 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.Correct.d_exec'45'xinstr_90
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
      (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.exec-xprog
d_exec'45'xprog_16 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_exec'45'xprog_16 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.Correct.d_exec'45'xprog_268
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
      (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.xreg-idx
d_xreg'45'idx_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_xreg'45'idx_20 ~v0 = du_xreg'45'idx_20
du_xreg'45'idx_20 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
du_xreg'45'idx_20
  = coe MAlonzo.Code.Once.Arith.Backend.Correct.du_xreg'45'idx_54
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._._%ˢ_
d__'37''738'__24 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'37''738'__24 v0
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._._/ˢ_
d__'47''738'__26 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'47''738'__26 v0
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._._⊕_
d__'8853'__28 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8853'__28 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8853'__26
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._._⊖_
d__'8854'__30 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8854'__30 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8854'__32
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._._⊗_
d__'8855'__32 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8855'__32 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8855'__38
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.fromℤ
d_fromℤ_34 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_fromℤ_34 v0
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ_20
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.sdiv2ᵏ
d_sdiv2'7503'_36 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_36 v0
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.shlᵂ
d_shl'7490'_38 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_shl'7490'_38 v0
  = coe
      MAlonzo.Code.Once.Word.d_shl'7490'_132
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.toℤ
d_toℤ_40 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_toℤ_40 v0
  = coe
      MAlonzo.Code.Once.Word.d_toℤ_50
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.⊝_
d_'8861'__42 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_'8861'__42 v0
  = coe
      MAlonzo.Code.Once.Word.d_'8861'__44
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.tgt
d_tgt_44 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  Maybe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10
d_tgt_44 ~v0 v1 = du_tgt_44 v1
du_tgt_44 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  Maybe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10
du_tgt_44 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xcmp'45'rrr_48 v1 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_50 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_52 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_54 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_56 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_58 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_60 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_62 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_64 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_66 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_68 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_70 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_72 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_74 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_76 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.¬d≡x
d_'172'd'8801'x_100 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'd'8801'x_100 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.additive-sa-inj
d_additive'45'sa'45'inj_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_additive'45'sa'45'inj_120 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.emit-program-++
d_emit'45'program'45''43''43'_138 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_emit'45'program'45''43''43'_138 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.block-shape
d_block'45'shape_154 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'shape_154 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.LoadOK
d_LoadOK_158 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 -> ()
d_LoadOK_158 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.LoadsWF
d_LoadsWF_178 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] -> ()
d_LoadsWF_178 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-++
d_lw'45''43''43'_194 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lw'45''43''43'_194 ~v0 ~v1 v2 ~v3 v4 v5
  = du_lw'45''43''43'_194 v2 v4 v5
du_lw'45''43''43'_194 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lw'45''43''43'_194 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_lw'45''43''43'_194 (coe v4) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-cat
d_lw'45'cat_218 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lw'45'cat_218 ~v0 ~v1 v2 ~v3 v4 v5 = du_lw'45'cat_218 v2 v4 v5
du_lw'45'cat_218 ::
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lw'45'cat_218 v0 v1 v2
  = coe
      du_lw'45''43''43'_194
      (coe
         MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_904
         (coe v0))
      (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-mul-choose
d_lw'45'mul'45'choose_234 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Maybe Integer -> AgdaAny
d_lw'45'mul'45'choose_234 ~v0 ~v1 v2
  = du_lw'45'mul'45'choose_234 v2
du_lw'45'mul'45'choose_234 :: Maybe Integer -> AgdaAny
du_lw'45'mul'45'choose_234 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-div-instr
d_lw'45'div'45'instr_242 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool -> AgdaAny
d_lw'45'div'45'instr_242 ~v0 ~v1 v2 = du_lw'45'div'45'instr_242 v2
du_lw'45'div'45'instr_242 :: Bool -> AgdaAny
du_lw'45'div'45'instr_242 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-rem-instr
d_lw'45'rem'45'instr_248 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool -> AgdaAny
d_lw'45'rem'45'instr_248 ~v0 ~v1 v2 = du_lw'45'rem'45'instr_248 v2
du_lw'45'rem'45'instr_248 :: Bool -> AgdaAny
du_lw'45'rem'45'instr_248 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-div-choose
d_lw'45'div'45'choose_256 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Maybe Integer -> Bool -> AgdaAny
d_lw'45'div'45'choose_256 ~v0 ~v1 v2 v3
  = du_lw'45'div'45'choose_256 v2 v3
du_lw'45'div'45'choose_256 :: Maybe Integer -> Bool -> AgdaAny
du_lw'45'div'45'choose_256 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_lw'45'div'45'instr_242 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-mul-op
d_lw'45'mul'45'op_270 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_lw'45'mul'45'op_270 ~v0 ~v1 ~v2 v3 = du_lw'45'mul'45'op_270 v3
du_lw'45'mul'45'op_270 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_lw'45'mul'45'op_270 v0
  = coe
      du_lw'45'mul'45'choose_234
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_pow2'63'_98 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-div-op
d_lw'45'div'45'op_280 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_lw'45'div'45'op_280 ~v0 ~v1 ~v2 v3 = du_lw'45'div'45'op_280 v3
du_lw'45'div'45'op_280 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_lw'45'div'45'op_280 v0
  = coe
      du_lw'45'div'45'choose_256
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_pow2'63'_98 (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_safe'45'divisor'63'_48
         (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-rem-op
d_lw'45'rem'45'op_290 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_lw'45'rem'45'op_290 ~v0 ~v1 ~v2 v3 = du_lw'45'rem'45'op_290 v3
du_lw'45'rem'45'op_290 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_lw'45'rem'45'op_290 v0
  = coe
      du_lw'45'rem'45'instr_248
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_safe'45'divisor'63'_48
         (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-bin
d_lw'45'bin_308 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lw'45'bin_308 ~v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10
  = du_lw'45'bin_308 v1 v2 v3 v4 v5 v6 v8 v9 v10
du_lw'45'bin_308 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lw'45'bin_308 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_lw'45'cat_218
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v0) (coe v1) (coe v3) (coe v4))
      (coe v6)
      (coe
         du_lw'45'cat_218
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
               (coe (0 :: Integer)) (coe v3))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe
            du_lw'45'cat_218
            (coe
               MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
               (coe v0) (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3))
               (coe v5))
            (coe v7) (coe v8)))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.lw-un
d_lw'45'un_334 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lw'45'un_334 ~v0 v1 v2 v3 v4 ~v5 v6 v7
  = du_lw'45'un_334 v1 v2 v3 v4 v6 v7
du_lw'45'un_334 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lw'45'un_334 v0 v1 v2 v3 v4 v5
  = coe
      du_lw'45'cat_218
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v0) (coe v1) (coe v2) (coe v3))
      (coe v4) (coe v5)
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.compile-loads
d_compile'45'loads_354 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_compile'45'loads_354 ~v0 v1 v2 v3 v4
  = du_compile'45'loads_354 v1 v2 v3 v4
du_compile'45'loads_354 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_compile'45'loads_354 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aflit_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v5
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) erased)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v5 v6
        -> coe
             seq (coe v1)
             (coe
                du_lw'45'bin_308 (coe v0) (coe v1) (coe v1) (coe v2) (coe v5)
                (coe v6)
                (coe du_compile'45'loads_354 (coe v0) (coe v1) (coe v2) (coe v5))
                (coe
                   du_compile'45'loads_354 (coe v0) (coe v1)
                   (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    du_lw'45'bin_308 (coe v0) (coe v1) (coe v1) (coe v2) (coe v5)
                    (coe v6)
                    (coe du_compile'45'loads_354 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       du_compile'45'loads_354 (coe v0) (coe v1)
                       (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    du_lw'45'bin_308 (coe v0) (coe v1) (coe v1) (coe v2) (coe v5)
                    (coe v6)
                    (coe du_compile'45'loads_354 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       du_compile'45'loads_354 (coe v0) (coe v1)
                       (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    du_lw'45'bin_308 (coe v0) (coe v1) (coe v1) (coe v2) (coe v5)
                    (coe v6)
                    (coe du_compile'45'loads_354 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       du_compile'45'loads_354 (coe v0) (coe v1)
                       (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          du_lw'45''43''43'_194
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit_28
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.Compile.du_mul'45'op_164 (coe v6)))
                          (coe du_lw'45'mul'45'op_270 (coe v6))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    du_lw'45'bin_308 (coe v0) (coe v1) (coe v1) (coe v2) (coe v5)
                    (coe v6)
                    (coe du_compile'45'loads_354 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       du_compile'45'loads_354 (coe v0) (coe v1)
                       (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    du_lw'45'bin_308 (coe v0) (coe v1) (coe v1) (coe v2) (coe v5)
                    (coe v6)
                    (coe du_compile'45'loads_354 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       du_compile'45'loads_354 (coe v0) (coe v1)
                       (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          du_lw'45''43''43'_194
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit_28
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.Compile.du_div'45'op_176 (coe v6)))
                          (coe du_lw'45'div'45'op_280 (coe v6))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    du_lw'45'bin_308 (coe v0) (coe v1) (coe v1) (coe v2) (coe v5)
                    (coe v6)
                    (coe du_compile'45'loads_354 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       du_compile'45'loads_354 (coe v0) (coe v1)
                       (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v4 v5
        -> coe
             du_lw'45'bin_308 (coe v0)
             (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
             (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v2) (coe v4)
             (coe v5)
             (coe
                du_compile'45'loads_354 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v2) (coe v4))
             (coe
                du_compile'45'loads_354 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v5))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   du_lw'45''43''43'_194
                   (coe
                      MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit_28
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Compile.du_rem'45'op_58 (coe v5)))
                   (coe du_lw'45'rem'45'op_290 (coe v5))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v5
        -> coe
             seq (coe v1)
             (coe
                du_lw'45'un_334 (coe v0) (coe v1) (coe v2) (coe v5)
                (coe du_compile'45'loads_354 (coe v0) (coe v1) (coe v2) (coe v5))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44 v4
        -> coe
             du_lw'45'un_334 (coe v0)
             (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v2) (coe v4)
             (coe
                du_compile'45'loads_354 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v2) (coe v4))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Arith.Machine.IR.C_acmp_46 v4 v5 v6
        -> coe
             du_lw'45'bin_308 (coe v0)
             (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
             (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v2) (coe v5)
             (coe v6)
             (coe
                du_compile'45'loads_354 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v2) (coe v5))
             (coe
                du_compile'45'loads_354 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.compile-loads-abs
d_compile'45'loads'45'abs_452 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_compile'45'loads'45'abs_452 ~v0 v1 v2 v3
  = du_compile'45'loads'45'abs_452 v1 v2 v3
du_compile'45'loads'45'abs_452 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_compile'45'loads'45'abs_452 v0 v1 v2
  = coe
      du_lw'45'cat_218
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v0) (coe v1) (coe (0 :: Integer)) (coe v2))
      (coe
         du_compile'45'loads_354 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.NonSpill
d_NonSpill_456 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 -> ()
d_NonSpill_456 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.scratch-unchanged
d_scratch'45'unchanged_464 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'unchanged_464 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.input-unchanged
d_input'45'unchanged_524 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'unchanged_524 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.xreg-idx-inj
d_xreg'45'idx'45'inj_904 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_904 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.frame-hyp
d_frame'45'hyp_914 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'hyp_914 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.no-tgt-hyp
d_no'45'tgt'45'hyp_932 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'tgt'45'hyp_932 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R
d_R_956 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_R_956 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.n≢j
d_n'8802'j_968 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_968 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.bin-value
d_bin'45'value_984 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'value_984 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.un-value
d_un'45'value_1094 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_un'45'value_1094 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.step-other
d_step'45'other_1162 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'other_1162 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.result-correct
d_result'45'correct_1196 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result'45'correct_1196 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-init
d_R'45'init_1216 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'init_1216 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-scratch
d_R'45'scratch_1230 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_R'45'scratch_1230 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-reload
d_R'45'step'45'reload_1250 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'reload_1250 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.leafWord
d_leafWord_1316 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> Integer
d_leafWord_1316 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                ~v38 ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 ~v48 v49 ~v50 v51
                v52
  = du_leafWord_1316 v0 v49 v51 v52
du_leafWord_1316 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> Integer
du_leafWord_1316 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'int_70
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20
             (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
             (coe v3)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_here'45'flt_72 -> coe v3
      MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'fst_80 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_leafWord_1316 (coe v0) (coe v8) (coe v7) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Shape.C_go'45'snd_88 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_leafWord_1316 (coe v0) (coe v9) (coe v7) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.leafWord-int
d_leafWord'45'int_1336 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leafWord'45'int_1336 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.leafWord-flt
d_leafWord'45'flt_1354 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leafWord'45'flt_1354 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-input
d_R'45'input_1368 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_R'45'input_1368 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-arg
d_R'45'step'45'arg_1390 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'arg_1390 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-farg
d_R'45'step'45'farg_1464 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'farg_1464 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf
d_Rf_1528 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_Rf_1528 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-full
d_R'45'step'45'full_1542 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'full_1542 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.input-frame
d_input'45'frame_2936 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'frame_2936 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.sa-slot-eq
d_sa'45'slot'45'eq_2956 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'slot'45'eq_2956 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.nonspill-sf
d_nonspill'45'sf_2978 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonspill'45'sf_2978 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.scratch-frame
d_scratch'45'frame_3008 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'frame_3008 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf-step
d_Rf'45'step_3400 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'step_3400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
                  ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                  ~v38 ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 ~v48 ~v49 v50
                  ~v51 ~v52 v53 v54
  = du_Rf'45'step_3400 v21 v50 v53 v54
du_Rf'45'step_3400 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'step_3400 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe v0 v1 v2 v9)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf-sim
d_Rf'45'sim_3428 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'sim_3428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
                 ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                 ~v38 ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 ~v48 ~v49 v50 v51
                 ~v52 v53 v54
  = du_Rf'45'sim_3428 v11 v21 v50 v51 v53 v54
du_Rf'45'sim_3428 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'sim_3428 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      [] -> coe v5
      (:) v6 v7
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    du_Rf'45'sim_3428 (coe v0) (coe v1) (coe v7) (coe v9)
                    (coe v0 v6 v4)
                    (coe du_Rf'45'step_3400 (coe v1) (coe v6) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-scratch-init
d_R'45'scratch'45'init_3466 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'scratch'45'init_3466 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf-init
d_Rf'45'init_3484 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'init_3484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                  ~v38 ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 ~v48 ~v49 ~v50
                  ~v51 v52 v53
  = du_Rf'45'init_3484 v52 v53
du_Rf'45'init_3484 ::
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'init_3484 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v0)))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.eb-++
d_eb'45''43''43'_3500 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eb'45''43''43'_3500 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.output-extract
d_output'45'extract_3522 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'extract_3522 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.pre
d_pre_3538 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]
d_pre_3538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37 ~v38
           ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 ~v48 v49 v50 ~v51 ~v52
           ~v53
  = du_pre_3538 v49 v50
du_pre_3538 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]
du_pre_3538 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_904
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe (0 :: Integer)) (coe v1))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.aPre
d_aPre_3540 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_aPre_3540 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37 ~v38
            ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 ~v48 v49 v50 v51 ~v52
            ~v53
  = du_aPre_3540 v0 v49 v50 v51
du_aPre_3540 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_aPre_3540 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Backend.Correct.d_exec'45'xprog_268
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
      (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
      (coe v1) (coe du_pre_3538 (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.Arith.Machine.AbsState.du_init_154 (coe v3))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.cPre
d_cPre_3542 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_cPre_3542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37 ~v38
            ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 ~v48 v49 v50 ~v51 v52
            ~v53
  = du_cPre_3542 v12 v49 v50 v52
du_cPre_3542 ::
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> AgdaAny
du_cPre_3542 v0 v1 v2 v3
  = coe v0 (coe du_pre_3538 (coe v1) (coe v2)) v3
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.blk≡
d_blk'8801'_3544 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blk'8801'_3544 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.ebk≡
d_ebk'8801'_3548 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ebk'8801'_3548 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.R'
d_R''_3552 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R''_3552 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.bvs'
d_bvs''_3558 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bvs''_3558 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.rr-eq
d_rr'45'eq_3562 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rr'45'eq_3562 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.body
d_body_3564 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body_3564 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.arith-block-correct
d_arith'45'block'45'correct_3576 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  AgdaAny ->
  (Maybe Integer -> Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   AgdaAny ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
   MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'block'45'correct_3576 = erased
