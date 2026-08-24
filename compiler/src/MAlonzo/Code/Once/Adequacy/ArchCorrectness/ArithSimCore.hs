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
      MAlonzo.Code.Once.Arith.Backend.Correct.d_exec'45'xinstr_86
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.exec-xprog
d_exec'45'xprog_16 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_exec'45'xprog_16 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.Correct.d_exec'45'xprog_198
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.xreg-idx
d_xreg'45'idx_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_xreg'45'idx_20 ~v0 = du_xreg'45'idx_20
du_xreg'45'idx_20 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
du_xreg'45'idx_20
  = coe MAlonzo.Code.Once.Arith.Backend.Correct.du_xreg'45'idx_50
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
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At._.⊝_
d_'8861'__40 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_'8861'__40 v0
  = coe
      MAlonzo.Code.Once.Word.d_'8861'__44
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.tgt
d_tgt_42 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  Maybe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10
d_tgt_42 ~v0 v1 = du_tgt_42 v1
du_tgt_42 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  Maybe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10
du_tgt_42 v0
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_56 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.¬d≡x
d_'172'd'8801'x_78 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'd'8801'x_78 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.additive-sa-inj
d_additive'45'sa'45'inj_98 ::
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
d_additive'45'sa'45'inj_98 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.emit-program-++
d_emit'45'program'45''43''43'_116 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_emit'45'program'45''43''43'_116 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.block-shape
d_block'45'shape_132 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'shape_132 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.NonSpill
d_NonSpill_136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 -> ()
d_NonSpill_136 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.scratch-unchanged
d_scratch'45'unchanged_144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'unchanged_144 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.input-unchanged
d_input'45'unchanged_182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'unchanged_182 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.xreg-idx-inj
d_xreg'45'idx'45'inj_456 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_456 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.frame-hyp
d_frame'45'hyp_466 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
d_frame'45'hyp_466 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.no-tgt-hyp
d_no'45'tgt'45'hyp_484 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'tgt'45'hyp_484 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R
d_R_508 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_R_508 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.n≢j
d_n'8802'j_520 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_520 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.bin-value
d_bin'45'value_536 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
d_bin'45'value_536 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.un-value
d_un'45'value_646 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
d_un'45'value_646 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.step-other
d_step'45'other_714 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
d_step'45'other_714 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.result-correct
d_result'45'correct_748 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
d_result'45'correct_748 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-init
d_R'45'init_768 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'init_768 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-scratch
d_R'45'scratch_782 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_R'45'scratch_782 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-reload
d_R'45'step'45'reload_802 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
d_R'45'step'45'reload_802 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-input
d_R'45'input_866 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_R'45'input_866 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-arg
d_R'45'step'45'arg_886 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'arg_886 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf
d_Rf_950 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny -> ()
d_Rf_950 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-step-full
d_R'45'step'45'full_964 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'step'45'full_964 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.input-frame
d_input'45'frame_1710 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  AgdaAny ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'frame_1710 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.sa-slot-eq
d_sa'45'slot'45'eq_1732 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sa'45'slot'45'eq_1732 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.nonspill-sf
d_nonspill'45'sf_1754 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
d_nonspill'45'sf_1754 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.scratch-frame
d_scratch'45'frame_1784 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
d_scratch'45'frame_1784 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf-step
d_Rf'45'step_2052 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'step_2052 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
                  ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                  ~v38 ~v39 v40 ~v41 v42 v43
  = du_Rf'45'step_2052 v21 v40 v42 v43
du_Rf'45'step_2052 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'step_2052 v0 v1 v2 v3
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
d_Rf'45'sim_2078 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'sim_2078 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
                 ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                 ~v38 ~v39 v40 ~v41 v42 v43
  = du_Rf'45'sim_2078 v11 v21 v40 v42 v43
du_Rf'45'sim_2078 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'sim_2078 v0 v1 v2 v3 v4
  = case coe v2 of
      [] -> coe v4
      (:) v5 v6
        -> coe
             du_Rf'45'sim_2078 (coe v0) (coe v1) (coe v6) (coe v0 v5 v3)
             (coe du_Rf'45'step_2052 (coe v1) (coe v5) (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.R-scratch-init
d_R'45'scratch'45'init_2110 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_R'45'scratch'45'init_2110 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.Rf-init
d_Rf'45'init_2128 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Rf'45'init_2128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37
                  ~v38 ~v39 ~v40 ~v41 v42 v43
  = du_Rf'45'init_2128 v42 v43
du_Rf'45'init_2128 ::
  AgdaAny ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Rf'45'init_2128 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v0)))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.eb-++
d_eb'45''43''43'_2144 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eb'45''43''43'_2144 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.output-extract
d_output'45'extract_2166 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'extract_2166 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.pre
d_pre_2182 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]
d_pre_2182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37 ~v38
           ~v39 v40 ~v41 ~v42 ~v43
  = du_pre_2182 v40
du_pre_2182 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]
du_pre_2182 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_532
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe (0 :: Integer)) (coe v0))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.aPre
d_aPre_2184 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_aPre_2184 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37 ~v38
            v39 v40 v41 ~v42 ~v43
  = du_aPre_2184 v0 v39 v40 v41
du_aPre_2184 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_aPre_2184 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Backend.Correct.d_exec'45'xprog_198
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
      (coe v1) (coe du_pre_2182 (coe v2))
      (coe MAlonzo.Code.Once.Arith.Machine.AbsState.du_init_154 (coe v3))
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.cPre
d_cPre_2186 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_cPre_2186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 ~v35 ~v36 ~v37 ~v38
            ~v39 v40 ~v41 v42 ~v43
  = du_cPre_2186 v12 v40 v42
du_cPre_2186 ::
  ([MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
   AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> AgdaAny
du_cPre_2186 v0 v1 v2 = coe v0 (coe du_pre_2182 (coe v1)) v2
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.blk≡
d_blk'8801'_2188 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blk'8801'_2188 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.ebk≡
d_ebk'8801'_2192 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ebk'8801'_2192 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.R'
d_R''_2196 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
d_R''_2196 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.bvs'
d_bvs''_2202 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bvs''_2202 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.rr-eq
d_rr'45'eq_2206 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rr'45'eq_2206 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core._.body
d_body_2208 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body_2208 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimCore.At.Core.arith-block-correct
d_arith'45'block'45'correct_2220 ::
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer) ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
   [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
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
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  ([MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'block'45'correct_2220 = erased
