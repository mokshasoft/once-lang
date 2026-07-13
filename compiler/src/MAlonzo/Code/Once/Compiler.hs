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

module MAlonzo.Code.Once.Compiler where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Once.Adequacy
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Compiler.VC._≋_
d__'8779'__6 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  ()
d__'8779'__6 = erased
-- Once.Compiler.VC._⊢R_
d__'8866'R__8 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d__'8866'R__8 = erased
-- Once.Compiler.VC.TraceAt
d_TraceAt_10 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_TraceAt_10 = erased
-- Once.Compiler.VC.Typed
d_Typed_12 :: ()
d_Typed_12 = erased
-- Once.Compiler.VC.accept-sound
d_accept'45'sound_14 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'sound_14 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Adequacy.Compile.du_accept'45'sound_542 v2
-- Once.Compiler.VC.bridgeᵈ
d_bridge'7496'_16 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'7496'_16 = erased
-- Once.Compiler.VC.codegen-asm-correct
d_codegen'45'asm'45'correct_18 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_codegen'45'asm'45'correct_18 = erased
-- Once.Compiler.VC.compile
d_compile_20 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_20
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile_178
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.compile-cr
d_compile'45'cr_22 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_686 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'cr_22
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'cr_140
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.compile-gm
d_compile'45'gm_24 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'gm_24
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'gm_166
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.compile-just-ir
d_compile'45'just'45'ir_26 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'just'45'ir_26 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'just'45'ir_630 v3
-- Once.Compiler.VC.compile-mir
d_compile'45'mir_28 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'mir_28
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'mir_152
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.correct
d_correct_30 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_30
  = coe MAlonzo.Code.Once.Adequacy.Compile.du_correct_482
-- Once.Compiler.VC.correct-cr
d_correct'45'cr_32 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'cr_32 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'45'cr_352 v4 v5 v7
-- Once.Compiler.VC.correct-gm
d_correct'45'gm_34 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm_34 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'45'gm_456 v0 v1 v2
-- Once.Compiler.VC.correct-mir
d_correct'45'mir_36 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'mir_36 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'45'mir_422 v0 v1 v2
      v3
-- Once.Compiler.VC.correctR
d_correctR_38 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR_38
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correctR_1020
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.correctR-complete
d_correctR'45'complete_40 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'complete_40 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correctR'45'complete_878
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6) v0 v1 v2
      v3
-- Once.Compiler.VC.correctR-sound
d_correctR'45'sound_42 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'sound_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correctR'45'sound_732 v2
-- Once.Compiler.VC.correctᵈ
d_correct'7496'_44 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correct'7496'_44
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'7496'_1072
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.exec
d_exec_46 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_exec_46
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_exec_130
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.main-realize-agrees
d_main'45'realize'45'agrees_48 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'realize'45'agrees_48 = erased
-- Once.Compiler.VC.module-to-asm-correct
d_module'45'to'45'asm'45'correct_50 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'to'45'asm'45'correct_50 = erased
-- Once.Compiler.VC.opt-trace
d_opt'45'trace_52 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opt'45'trace_52 = erased
-- Once.Compiler.VC.pw-just-inv
d_pw'45'just'45'inv_54 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  Maybe
    (Integer ->
     [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pw'45'just'45'inv_54 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_pw'45'just'45'inv_528 v1
-- Once.Compiler.VC.pw-just-rel
d_pw'45'just'45'rel_56 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pw'45'just'45'rel_56 = erased
-- Once.Compiler.VC.sd-bridge
d_sd'45'bridge_58 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sd'45'bridge_58 = erased
-- Once.Compiler.VC.string-to-bytes
d_string'45'to'45'bytes_60 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_60
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_string'45'to'45'bytes_136
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_62 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_62 = erased
-- Once.Compiler.VC.⟦_⟧A_
d_'10214'_'10215'A__64 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215'A__64
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215'A__186
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.d_arch'45'correctness_8)
-- Once.Compiler.VC.⟦_⟧ˢ
d_'10214'_'10215''738'_66 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215''738'_66
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''738'_588
-- Once.Compiler.VC.⟦_⟧ᵈ
d_'10214'_'10215''7496'_68 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215''7496'_68
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''7496'_1036
-- Once.Compiler.VC.⟦_⟧⊥
d_'10214'_'10215''8869'_70 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869'_70
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869'_260
-- Once.Compiler.VC.⟦_⟧⊥-ir
d_'10214'_'10215''8869''45'ir_72 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'ir_72
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869''45'ir_252
-- Once.Compiler.VC.⟦_⟧⊥-m
d_'10214'_'10215''8869''45'm_74 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'm_74
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869''45'm_256
-- Once.Compiler.VC.⟦⟧⊥-ir-sound
d_'10214''10215''8869''45'ir'45'sound_76 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'ir'45'sound_76 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214''10215''8869''45'ir'45'sound_270
      v0
-- Once.Compiler.VC.⟦⟧⊥-just
d_'10214''10215''8869''45'just_78 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just_78 = erased
-- Once.Compiler.VC.⟦⟧⊥-m-sound
d_'10214''10215''8869''45'm'45'sound_80 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'm'45'sound_80 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214''10215''8869''45'm'45'sound_286
      v0
-- Once.Compiler.VC.⟦⟧⊥-sound
d_'10214''10215''8869''45'sound_82 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'sound_82 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214''10215''8869''45'sound_302
      v0
-- Once.Compiler.once-compiler
d_once'45'compiler_84 ::
  MAlonzo.Code.Once.Adequacy.T_CorrectCompiler_4
d_once'45'compiler_84
  = coe
      MAlonzo.Code.Once.Adequacy.C_constructor_78
      (coe
         MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''7496'_1036)
      (coe
         MAlonzo.Code.Once.Adequacy.Compile.du_exec_130
         (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6))
      (coe
         MAlonzo.Code.Once.Adequacy.Compile.du_compile_178
         (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6))
      (coe
         MAlonzo.Code.Once.Adequacy.Compile.du_correct'7496'_1072
         (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6))
