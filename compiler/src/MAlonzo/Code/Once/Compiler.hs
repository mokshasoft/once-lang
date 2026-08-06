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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Compiler.VC._≋_
d__'8779'__20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  ()
d__'8779'__20 = erased
-- Once.Compiler.VC._⊢R_
d__'8866'R__22 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d__'8866'R__22 = erased
-- Once.Compiler.VC.TraceAt
d_TraceAt_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_TraceAt_24 = erased
-- Once.Compiler.VC.Typed
d_Typed_26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  ()
d_Typed_26 = erased
-- Once.Compiler.VC.accept-sound
d_accept'45'sound_28 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'sound_28 ~v0 ~v1 ~v2 ~v3 ~v4 = du_accept'45'sound_28
du_accept'45'sound_28 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'sound_28 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Adequacy.Compile.du_accept'45'sound_542 v2
-- Once.Compiler.VC.bridgeᵈ
d_bridge'7496'_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'7496'_30 = erased
-- Once.Compiler.VC.codegen-asm-correct
d_codegen'45'asm'45'correct_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_codegen'45'asm'45'correct_32 = erased
-- Once.Compiler.VC.compile
d_compile_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_34 ~v0 ~v1 ~v2 ~v3 ~v4 = du_compile_34
du_compile_34 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile_34
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile_178
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.compile-cr
d_compile'45'cr_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_722 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'cr_36 ~v0 ~v1 ~v2 ~v3 ~v4 = du_compile'45'cr_36
du_compile'45'cr_36 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_722 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'cr_36
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'cr_140
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.compile-gm
d_compile'45'gm_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'gm_38 ~v0 ~v1 ~v2 ~v3 ~v4 = du_compile'45'gm_38
du_compile'45'gm_38 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'gm_38
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'gm_166
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.compile-just-ir
d_compile'45'just'45'ir_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'just'45'ir_40 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_compile'45'just'45'ir_40
du_compile'45'just'45'ir_40 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compile'45'just'45'ir_40 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'just'45'ir_630 v3
-- Once.Compiler.VC.compile-mir
d_compile'45'mir_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'mir_42 ~v0 ~v1 ~v2 ~v3 ~v4 = du_compile'45'mir_42
du_compile'45'mir_42 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'mir_42
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_compile'45'mir_152
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.correct
d_correct_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_44 ~v0 ~v1 ~v2 ~v3 ~v4 = du_correct_44
du_correct_44 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct_44
  = coe MAlonzo.Code.Once.Adequacy.Compile.du_correct_482
-- Once.Compiler.VC.correct-cr
d_correct'45'cr_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_722 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'cr_46 ~v0 ~v1 ~v2 ~v3 ~v4 = du_correct'45'cr_46
du_correct'45'cr_46 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_722 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'cr_46 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'45'cr_352 v4 v5 v7
-- Once.Compiler.VC.correct-gm
d_correct'45'gm_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_correct'45'gm_48 ~v0 ~v1 ~v2 ~v3 ~v4 = du_correct'45'gm_48
du_correct'45'gm_48 ::
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
du_correct'45'gm_48 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'45'gm_456 v0 v1 v2
-- Once.Compiler.VC.correct-mir
d_correct'45'mir_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
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
d_correct'45'mir_50 ~v0 ~v1 ~v2 ~v3 ~v4 = du_correct'45'mir_50
du_correct'45'mir_50 ::
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
du_correct'45'mir_50 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'45'mir_422 v0 v1 v2
      v3
-- Once.Compiler.VC.correctR
d_correctR_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR_52 ~v0 ~v1 ~v2 ~v3 ~v4 = du_correctR_52
du_correctR_52 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR_52
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correctR_1020
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.correctR-complete
d_correctR'45'complete_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'complete_54 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_correctR'45'complete_54
du_correctR'45'complete_54 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR'45'complete_54 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correctR'45'complete_878
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6) v0 v1 v2
      v3
-- Once.Compiler.VC.correctR-sound
d_correctR'45'sound_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'sound_56 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_correctR'45'sound_56
du_correctR'45'sound_56 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR'45'sound_56 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correctR'45'sound_732 v2
-- Once.Compiler.VC.correctᵈ
d_correct'7496'_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correct'7496'_58 ~v0 ~v1 ~v2 ~v3 ~v4 = du_correct'7496'_58
du_correct'7496'_58 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correct'7496'_58
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_correct'7496'_1072
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.exec
d_exec_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_exec_60 ~v0 ~v1 ~v2 ~v3 ~v4 = du_exec_60
du_exec_60 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_exec_60
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_exec_130
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.main-realize-agrees
d_main'45'realize'45'agrees_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'realize'45'agrees_62 = erased
-- Once.Compiler.VC.module-to-asm-correct
d_module'45'to'45'asm'45'correct_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'to'45'asm'45'correct_64 = erased
-- Once.Compiler.VC.opt-trace
d_opt'45'trace_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opt'45'trace_66 = erased
-- Once.Compiler.VC.pw-just-inv
d_pw'45'just'45'inv_68 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  Maybe
    (Integer ->
     [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pw'45'just'45'inv_68 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_pw'45'just'45'inv_68
du_pw'45'just'45'inv_68 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  Maybe
    (Integer ->
     [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pw'45'just'45'inv_68 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_pw'45'just'45'inv_528 v1
-- Once.Compiler.VC.pw-just-rel
d_pw'45'just'45'rel_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pw'45'just'45'rel_70 = erased
-- Once.Compiler.VC.sd-bridge
d_sd'45'bridge_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sd'45'bridge_72 = erased
-- Once.Compiler.VC.string-to-bytes
d_string'45'to'45'bytes_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_74 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_string'45'to'45'bytes_74
du_string'45'to'45'bytes_74 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_string'45'to'45'bytes_74
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_string'45'to'45'bytes_136
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6)
-- Once.Compiler.VC.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_76 = erased
-- Once.Compiler.VC.⟦_⟧A_
d_'10214'_'10215'A__78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215'A__78 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215'A__186
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.d_arch'45'correctness_30
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Compiler.VC.⟦_⟧ˢ
d_'10214'_'10215''738'_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215''738'_80 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'10214'_'10215''738'_80
du_'10214'_'10215''738'_80 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_'10214'_'10215''738'_80
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''738'_588
-- Once.Compiler.VC.⟦_⟧ᵈ
d_'10214'_'10215''7496'_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215''7496'_82 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'10214'_'10215''7496'_82
du_'10214'_'10215''7496'_82 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_'10214'_'10215''7496'_82
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''7496'_1036
-- Once.Compiler.VC.⟦_⟧⊥
d_'10214'_'10215''8869'_84 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869'_84 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'10214'_'10215''8869'_84
du_'10214'_'10215''8869'_84 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
du_'10214'_'10215''8869'_84
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869'_260
-- Once.Compiler.VC.⟦_⟧⊥-ir
d_'10214'_'10215''8869''45'ir_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'ir_86 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'10214'_'10215''8869''45'ir_86
du_'10214'_'10215''8869''45'ir_86 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
du_'10214'_'10215''8869''45'ir_86
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869''45'ir_252
-- Once.Compiler.VC.⟦_⟧⊥-m
d_'10214'_'10215''8869''45'm_88 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'm_88 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'10214'_'10215''8869''45'm_88
du_'10214'_'10215''8869''45'm_88 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
du_'10214'_'10215''8869''45'm_88
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214'_'10215''8869''45'm_256
-- Once.Compiler.VC.⟦⟧⊥-ir-sound
d_'10214''10215''8869''45'ir'45'sound_90 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'ir'45'sound_90 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'10214''10215''8869''45'ir'45'sound_90
du_'10214''10215''8869''45'ir'45'sound_90 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'ir'45'sound_90 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214''10215''8869''45'ir'45'sound_270
      v0
-- Once.Compiler.VC.⟦⟧⊥-just
d_'10214''10215''8869''45'just_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just_92 = erased
-- Once.Compiler.VC.⟦⟧⊥-m-sound
d_'10214''10215''8869''45'm'45'sound_94 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'm'45'sound_94 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'10214''10215''8869''45'm'45'sound_94
du_'10214''10215''8869''45'm'45'sound_94 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'm'45'sound_94 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214''10215''8869''45'm'45'sound_286
      v0
-- Once.Compiler.VC.⟦⟧⊥-sound
d_'10214''10215''8869''45'sound_96 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'sound_96 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'10214''10215''8869''45'sound_96
du_'10214''10215''8869''45'sound_96 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'sound_96 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.du_'10214''10215''8869''45'sound_302
      v0
-- Once.Compiler.once-compiler
d_once'45'compiler_98 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_264 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext.T_RunAt_258 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation.T_CompiledCorr_604 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.T_CorrectCompiler_4
d_once'45'compiler_98 ~v0 ~v1 ~v2 ~v3 ~v4 = du_once'45'compiler_98
du_once'45'compiler_98 ::
  MAlonzo.Code.Once.Adequacy.T_CorrectCompiler_4
du_once'45'compiler_98
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
