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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Backend.Correct
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
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
      MAlonzo.Code.Once.Arith.Backend.Correct.d_exec'45'xprog_258
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_56 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_58 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_60 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_62 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_64 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_66 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_68 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_70 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_72 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_74 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.¬d≡x
d_'172'd'8801'x_98 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'd'8801'x_98 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.additive-sa-inj
d_additive'45'sa'45'inj_118 ::
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
d_additive'45'sa'45'inj_118 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.emit-program-++
d_emit'45'program'45''43''43'_136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_emit'45'program'45''43''43'_136 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.block-shape
d_block'45'shape_152 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'shape_152 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.NonSpill
d_NonSpill_156 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 -> ()
d_NonSpill_156 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.scratch-unchanged
d_scratch'45'unchanged_164 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'unchanged_164 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.IsFloatArg
d_IsFloatArg_216 a0 a1 = ()
data T_IsFloatArg_216 = C_fx'45'farg_222
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.input-unchanged
d_input'45'unchanged_230 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'unchanged_230 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.xreg-idx-inj
d_xreg'45'idx'45'inj_588 ::
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
d_xreg'45'idx'45'inj_588 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.frame-hyp
d_frame'45'hyp_598 ::
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
d_frame'45'hyp_598 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.no-tgt-hyp
d_no'45'tgt'45'hyp_616 ::
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
d_no'45'tgt'45'hyp_616 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R
d_R_640 ::
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
d_R_640 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.n≢j
d_n'8802'j_652 ::
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
d_n'8802'j_652 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.bin-value
d_bin'45'value_668 ::
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
d_bin'45'value_668 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.un-value
d_un'45'value_778 ::
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
d_un'45'value_778 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.step-other
d_step'45'other_846 ::
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
d_step'45'other_846 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.result-correct
d_result'45'correct_880 ::
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
d_result'45'correct_880 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-init
d_R'45'init_900 ::
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
d_R'45'init_900 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-scratch
d_R'45'scratch_914 ::
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
d_R'45'scratch_914 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-reload
d_R'45'step'45'reload_934 ::
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
d_R'45'step'45'reload_934 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-input
d_R'45'input_998 ::
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
d_R'45'input_998 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-arg
d_R'45'step'45'arg_1018 ::
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
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'arg_1018 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf
d_Rf_1082 ::
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
d_Rf_1082 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.float-arg-sim
d_float'45'arg'45'sim_1096
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.float-arg-sim"
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-full
d_R'45'step'45'full_1106 ::
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'full_1106 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.input-frame
d_input'45'frame_2296 ::
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
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'frame_2296 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.sa-slot-eq
d_sa'45'slot'45'eq_2318 ::
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
d_sa'45'slot'45'eq_2318 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.nonspill-sf
d_nonspill'45'sf_2340 ::
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
d_nonspill'45'sf_2340 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.scratch-frame
d_scratch'45'frame_2370 ::
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
d_scratch'45'frame_2370 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf-step
d_Rf'45'step_2746 ::
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'step_2746 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
                  ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                  ~v38 ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 v48 ~v49 v50 v51
  = du_Rf'45'step_2746 v21 v48 v50 v51
du_Rf'45'step_2746 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'step_2746 v0 v1 v2 v3
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
d_Rf'45'sim_2772 ::
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
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'sim_2772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
                 ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                 ~v38 ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 v48 ~v49 v50 v51
  = du_Rf'45'sim_2772 v11 v21 v48 v50 v51
du_Rf'45'sim_2772 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'sim_2772 v0 v1 v2 v3 v4
  = case coe v2 of
      [] -> coe v4
      (:) v5 v6
        -> coe
             du_Rf'45'sim_2772 (coe v0) (coe v1) (coe v6) (coe v0 v5 v3)
             (coe du_Rf'45'step_2746 (coe v1) (coe v5) (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-scratch-init
d_R'45'scratch'45'init_2804 ::
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
d_R'45'scratch'45'init_2804 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf-init
d_Rf'45'init_2822 ::
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
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'init_2822 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                  ~v38 ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 ~v48 ~v49 v50 v51
  = du_Rf'45'init_2822 v50 v51
du_Rf'45'init_2822 ::
  AgdaAny ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'init_2822 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v0)))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.eb-++
d_eb'45''43''43'_2838 ::
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
d_eb'45''43''43'_2838 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.output-extract
d_output'45'extract_2860 ::
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
d_output'45'extract_2860 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.pre
d_pre_2876 ::
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
d_pre_2876 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37 ~v38
           ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 v48 ~v49 ~v50 ~v51
  = du_pre_2876 v48
du_pre_2876 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]
du_pre_2876 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_870
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
         (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe (0 :: Integer))
         (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.aPre
d_aPre_2878 ::
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
d_aPre_2878 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37 ~v38
            ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 v47 v48 v49 ~v50 ~v51
  = du_aPre_2878 v0 v47 v48 v49
du_aPre_2878 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_aPre_2878 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Backend.Correct.d_exec'45'xprog_258
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
      (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
      (coe v1) (coe du_pre_2876 (coe v2))
      (coe MAlonzo.Code.Once.Arith.Machine.AbsState.du_init_154 (coe v3))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.cPre
d_cPre_2880 ::
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
d_cPre_2880 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37 ~v38
            ~v39 ~v40 ~v41 ~v42 ~v43 ~v44 ~v45 ~v46 ~v47 v48 ~v49 v50 ~v51
  = du_cPre_2880 v12 v48 v50
du_cPre_2880 ::
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> AgdaAny
du_cPre_2880 v0 v1 v2 = coe v0 (coe du_pre_2876 (coe v1)) v2
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.blk≡
d_blk'8801'_2882 ::
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
d_blk'8801'_2882 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.ebk≡
d_ebk'8801'_2886 ::
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
d_ebk'8801'_2886 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.R'
d_R''_2890 ::
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
d_R''_2890 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.bvs'
d_bvs''_2896 ::
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
d_bvs''_2896 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.rr-eq
d_rr'45'eq_2900 ::
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
d_rr'45'eq_2900 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.body
d_body_2902 ::
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
d_body_2902 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.arith-block-correct
d_arith'45'block'45'correct_2914 ::
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
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'block'45'correct_2914 = erased
