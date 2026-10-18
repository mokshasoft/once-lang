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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64 where

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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimRiscV64
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.RegRoles
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.CPU.RiscV64
import qualified MAlonzo.Code.Once.Adequacy.MachineTrace
import qualified MAlonzo.Code.Once.Arith.Backend.CallAnswer
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceMachine
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.File
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceTr
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Memory.StackSlots
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Trace
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg

-- Once.Adequacy.ArchCorrectness.RiscV64.rv64-frame-semantics
d_rv64'45'frame'45'semantics_38 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
d_rv64'45'frame'45'semantics_38 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10
  = du_rv64'45'frame'45'semantics_38 v2
du_rv64'45'frame'45'semantics_38 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
du_rv64'45'frame'45'semantics_38 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_246
      (coe v0)
-- Once.Adequacy.ArchCorrectness.RiscV64.stack-top-in-stack
d_stack'45'top'45'in'45'stack_1912
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.RiscV64.stack-top-in-stack"
-- Once.Adequacy.ArchCorrectness.RiscV64.entry-frame-riscv64
d_entry'45'frame'45'riscv64_1914 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_entry'45'frame'45'riscv64_1914 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.C_stack'45'addr_24
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_stack'45'top_448)
      (coe
         d_stack'45'top'45'in'45'stack_1912 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
         v10)
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.BlockRunsT
d_BlockRunsT_1918 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  ()
d_BlockRunsT_1918 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.IOC
d_IOC_1920 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  ()
d_IOC_1920 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.blocks-prefix
d_blocks'45'prefix_1922 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'prefix_1922 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10
  = du_blocks'45'prefix_1922
du_blocks'45'prefix_1922 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'prefix_1922 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_blocks'45'prefix_2178
      v2 v3
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-alloc
d_entry'45'alloc_1924 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_entry'45'alloc_1924 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'alloc_2098
      (coe
         d_entry'45'frame'45'riscv64_1914 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
         (coe v10))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-bf
d_entry'45'bf_1926 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_entry'45'bf_1926 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45'bf_1926
du_entry'45'bf_1926 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
du_entry'45'bf_1926 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'bf_2122
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-blocks
d_entry'45'blocks_1928 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_entry'45'blocks_1928 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45'blocks_1928 v0 v2
du_entry'45'blocks_1928 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_entry'45'blocks_1928 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'blocks_2248
      (coe v0) (coe du_rv64'45'frame'45'semantics_38 (coe v1))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-labels
d_entry'45'labels_1930 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'labels_1930 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-loc
d_entry'45'loc_1932 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_1932 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45'loc_1932
du_entry'45'loc_1932 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_1932
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'loc_2104
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-nh
d_entry'45'nh_1934 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_1934 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-ns
d_entry'45'ns_1936 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_entry'45'ns_1936 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45'ns_1936
du_entry'45'ns_1936 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_entry'45'ns_1936 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'ns_2118
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-regs
d_entry'45'regs_1938 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_120
d_entry'45'regs_1938 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45'regs_1938
du_entry'45'regs_1938 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_120
du_entry'45'regs_1938
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'regs_2106
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-s
d_entry'45's_1940 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_entry'45's_1940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_entry'45's_1940
du_entry'45's_1940 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
du_entry'45's_1940
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45's_2108
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-span
d_entry'45'span_1942 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'span_1942 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-vr
d_entry'45'vr_1944 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102
d_entry'45'vr_1944 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'vr_2312
      (coe v0) (coe v1) (coe du_rv64'45'frame'45'semantics_38 (coe v2))
      (coe
         d_entry'45'frame'45'riscv64_1914 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
         (coe v10))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.entry-witness
d_entry'45'witness_1946 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286
d_entry'45'witness_1946 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'witness_2286
      (coe v0) (coe v1) (coe du_rv64'45'frame'45'semantics_38 (coe v2))
      (coe
         d_entry'45'frame'45'riscv64_1914 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
         (coe v10))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.flat-ends
d_flat'45'ends_1948 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   AgdaAny ->
   Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
    Integer ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286) ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'ends_1948 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.fns-slot-stable
d_fns'45'slot'45'stable_1950 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'slot'45'stable_1950 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_fns'45'slot'45'stable_1950 v2
du_fns'45'slot'45'stable_1950 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fns'45'slot'45'stable_1950 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_fns'45'slot'45'stable_2258
      (coe du_rv64'45'frame'45'semantics_38 (coe v0))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.image
d_image_1952 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_image_1952 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_image_1952 v0 v1
du_image_1952 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_image_1952 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image_2138
      (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.image-slot-stable
d_image'45'slot'45'stable_1954 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'slot'45'stable_1954 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                               ~v10
  = du_image'45'slot'45'stable_1954 v0 v1 v2
du_image'45'slot'45'stable_1954 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_image'45'slot'45'stable_1954 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image'45'slot'45'stable_2270
      (coe v0) (coe v1) (coe du_rv64'45'frame'45'semantics_38 (coe v2))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.main-blocks
d_main'45'blocks_1956 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_main'45'blocks_1956 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_main'45'blocks_1956 v0 v2
du_main'45'blocks_1956 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_main'45'blocks_1956 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_main'45'blocks_2134
      (coe v0) (coe du_rv64'45'frame'45'semantics_38 (coe v1))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.main-flat
d_main'45'flat_1958 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_main'45'flat_1958 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_main'45'flat_2276
      (coe v0) (coe du_rv64'45'frame'45'semantics_38 (coe v2))
      (coe
         d_entry'45'frame'45'riscv64_1914 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
         (coe v10))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.span-prefix
d_span'45'prefix_1960 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_span'45'prefix_1960 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.start-flat
d_start'45'flat_1962 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_start'45'flat_1962 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_start'45'flat_2274
      (coe
         d_entry'45'frame'45'riscv64_1914 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
         (coe v10))
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.top-pre
d_top'45'pre_1964 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_top'45'pre_1964 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_top'45'pre_1964 v0
du_top'45'pre_1964 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_top'45'pre_1964 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_top'45'pre_2128
      (coe v0)
-- Once.Adequacy.ArchCorrectness.RiscV64.FFOr.σFS
d_σFS_1966 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_σFS_1966 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_σFS_1966 v2
du_σFS_1966 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_σFS_1966 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_σFS_2298
      (coe du_rv64'45'frame'45'semantics_38 (coe v0))
-- Once.Adequacy.ArchCorrectness.RiscV64.asR
d_asR_1968 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_asR_1968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_asR_1968
du_asR_1968 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
du_asR_1968
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6
      (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
-- Once.Adequacy.ArchCorrectness.RiscV64._.CompiledCorr
d_CompiledCorr_1972 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Once.Adequacy.ArchCorrectness.RiscV64._.EntryLike
d_EntryLike_1976 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_EntryLike_1976 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._.RunAt
d_RunAt_1978 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.Adequacy.ArchCorrectness.RiscV64._.CompiledCorr.code-eq
d_code'45'eq_1990 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_1990 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._.CompiledCorr.dataCorr
d_dataCorr_1992 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_dataCorr_1992 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
      (coe v0)
-- Once.Adequacy.ArchCorrectness.RiscV64._.CompiledCorr.pc-off
d_pc'45'off_1994 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_1994 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._.CompiledCorr.ret-eq
d_ret'45'eq_1996 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  AgdaAny
d_ret'45'eq_1996 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_654
      (coe v0)
-- Once.Adequacy.ArchCorrectness.RiscV64._.RunAt.run-emit
d_run'45'emit_2000 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_2000 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._.RunAt.run-ir
d_run'45'ir_2002 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_2002 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_436
      (coe v0)
-- Once.Adequacy.ArchCorrectness.RiscV64._.RunAt.run-linked
d_run'45'linked_2004 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'linked_2004 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_440
      (coe v0)
-- Once.Adequacy.ArchCorrectness.RiscV64._.RunAt.run-reach
d_run'45'reach_2006 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_360
d_run'45'reach_2006 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_442
      (coe v0)
-- Once.Adequacy.ArchCorrectness.RiscV64._.RunAt.run-tbl
d_run'45'tbl_2008 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_run'45'tbl_2008 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_434
      (coe v0)
-- Once.Adequacy.ArchCorrectness.RiscV64._.FlatWF
d_FlatWF_2020 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatWF_2020 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._.sv-below
d_sv'45'below_2022 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_2022 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._.FlatRegTag
d_FlatRegTag_2026 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatRegTag_2026 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.code-map
d_code'45'map_2028 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_code'45'map_2028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                   v12
  = du_code'45'map_2028 v11 v12
du_code'45'map_2028 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
du_code'45'map_2028 v0 v1
  = coe
      du_pick_2038
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_find'45'label_532
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Label.C_callee_34
            (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v1))))
-- Once.Adequacy.ArchCorrectness.RiscV64._.pick
d_pick_2038 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer -> Integer
d_pick_2038 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13
  = du_pick_2038 v13
du_pick_2038 :: Maybe Integer -> Integer
du_pick_2038 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.entry-view
d_entry'45'view_2042 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
d_entry'45'view_2042 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11
  = du_entry'45'view_2042 v11
du_entry'45'view_2042 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
du_entry'45'view_2042 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_mkHV_518
      (\ v1 ->
         MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_slot'45'to'45'disp_60
           (coe
              MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_46 (coe v1)))
      (0 :: Integer) (coe du_code'45'map_2028 (coe v0)) erased
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_stack'45'top_448
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Adequacy.ArchCorrectness.RiscV64._.suc-law
d_suc'45'law_2052 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'law_2052 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.entry-frame-base
d_entry'45'frame'45'base_2062 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'frame'45'base_2062 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.entry-corr
d_entry'45'corr_2066 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628
d_entry'45'corr_2066 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11
  = du_entry'45'corr_2066
du_entry'45'corr_2066 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628
du_entry'45'corr_2066
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.C_constructor_662
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_constructor_1176
         erased erased erased
         (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_stack'45'top_448))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_stack'45'top_448))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.RiscV64._.cong-pick
d_cong'45'pick_2078 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'45'pick_2078 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.entry-wf
d_entry'45'wf_2112 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736
d_entry'45'wf_2112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11
  = du_entry'45'wf_2112
du_entry'45'wf_2112 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736
du_entry'45'wf_2112
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.C_constructor_778
      (coe du_reg'45'below_2122)
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.RiscV64._.reg-below
d_reg'45'below_2122 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_reg'45'below_2122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 v12
  = du_reg'45'below_2122 v12
du_reg'45'below_2122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
du_reg'45'below_2122 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.RiscV64.entry-regtag
d_entry'45'regtag_2136 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524
d_entry'45'regtag_2136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11
  = du_entry'45'regtag_2136
du_entry'45'regtag_2136 ::
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524
du_entry'45'regtag_2136
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.C_mkRegTagWF_536
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         erased)
-- Once.Adequacy.ArchCorrectness.RiscV64.entry-like
d_entry'45'like_2142 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'like_2142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11
  = du_entry'45'like_2142
du_entry'45'like_2142 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'like_2142
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))))))
-- Once.Adequacy.ArchCorrectness.RiscV64._.no-ptr
d_no'45'ptr_2154 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'ptr_2154 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.conc-tr
d_conc'45'tr_2180 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_conc'45'tr_2180 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  ~v15
  = du_conc'45'tr_2180
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_conc'45'tr_2180 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_conc'45'tr_2180 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14
  = coe
      MAlonzo.Code.Once.Adequacy.MachineTrace.du_reaches'45''8776'_426
      (coe
         MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_δ_92
         (coe
            (\ v15 ->
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_halted_438
                 (coe v15)))
         (coe
            (\ v15 ->
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_pc_436 (coe v15)))
         (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_fetch_506)
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_execInstr_564)
         (coe
            MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace.d_matchCall_10)
         (coe
            MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace.d_ret'45'call_26
            (coe
               MAlonzo.Code.Once.Arith.Backend.CallAnswer.du_answer'45'at_158
               (coe v2)
               (coe
                  MAlonzo.Code.Once.Adequacy.CPU.RiscV64.d_call'45'at'45'riscv64_10)))
         (coe
            MAlonzo.Code.Data.Product.Base.du_uncurry_244
            (\ v15 v16 v17 ->
               coe
                 MAlonzo.Code.Once.Arith.Backend.RiscV64.Dispatch.du_dispatch'45'arith_18
                 (\ v18 v19 v20 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimRiscV64.du_val'45'riscv64_324
                      v18 v19)
                 v15 v17))
         (coe MAlonzo.Code.Once.Adequacy.CPU.RiscV64.d_ev'45'riscv64_8)
         (coe
            MAlonzo.Code.Once.Adequacy.CPU.RiscV64.d_block'45'env_12
            (coe MAlonzo.Code.Once.Compile.d_blocks'45'riscv64_998 (coe v12)))
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'trace_146
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image_2138
               (coe v0) (coe v1) (coe v13))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_initState_454))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Lang.Event.d_toEvent_164)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v2)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
               (coe
                  MAlonzo.Code.Once.Denotation.Program.d_runIR_392
                  (coe
                     MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                     (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
                  (coe MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262 (coe v2))
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                     (coe v13))))))
      (coe
         MAlonzo.Code.Once.Denotation.TraceTr.du_endOf_58
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v2)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
               (coe
                  MAlonzo.Code.Once.Denotation.Program.d_runIR_392
                  (coe
                     MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                     (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
                  (coe MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262 (coe v2))
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                     (coe v13))))))
      (coe
         MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_ended'45'reaches_590
         (coe
            (\ v15 ->
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_halted_438
                 (coe v15)))
         (coe
            (\ v15 ->
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_pc_436 (coe v15)))
         (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_fetch_506)
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_execInstr_564)
         (coe
            MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace.d_matchCall_10)
         (coe
            MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace.d_ret'45'call_26
            (coe
               MAlonzo.Code.Once.Arith.Backend.CallAnswer.du_answer'45'at_158
               (coe v2)
               (coe
                  MAlonzo.Code.Once.Adequacy.CPU.RiscV64.d_call'45'at'45'riscv64_10)))
         (coe
            MAlonzo.Code.Data.Product.Base.du_uncurry_244
            (\ v15 v16 v17 ->
               coe
                 MAlonzo.Code.Once.Arith.Backend.RiscV64.Dispatch.du_dispatch'45'arith_18
                 (\ v18 v19 v20 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimRiscV64.du_val'45'riscv64_324
                      v18 v19)
                 v15 v17))
         (coe MAlonzo.Code.Once.Adequacy.CPU.RiscV64.d_ev'45'riscv64_8)
         (coe
            MAlonzo.Code.Once.Adequacy.CPU.RiscV64.d_block'45'env_12
            (coe MAlonzo.Code.Once.Compile.d_blocks'45'riscv64_998 (coe v12)))
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'trace_146
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image_2138
               (coe v0) (coe v1) (coe v13)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_agree_2198 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) erased))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_initState_454)
         (coe
            MAlonzo.Code.Once.Denotation.TraceTr.du_endOf_58
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v2)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.d_runIR_392
                     (coe
                        MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                        (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12))
                     (coe MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262 (coe v2))
                     (coe
                        MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                        (coe v13)))))))
-- Once.Adequacy.ArchCorrectness.RiscV64._.run₀
d_run'8320'_2196 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418
d_run'8320'_2196 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 v13 v14 ~v15
  = du_run'8320'_2196 v1 v13 v14
du_run'8320'_2196 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418
du_run'8320'_2196 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_444
      v0 v1 v2
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'start_368
         (coe du_entry'45'like_2142))
-- Once.Adequacy.ArchCorrectness.RiscV64._.agree
d_agree_2198 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree_2198 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.du_events'45'agree'45'start_4904
      (coe v0) (coe du_rv64'45'frame'45'semantics_38 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_70)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_constructor_120
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.RegRoles.d_riscv64'45'roles_12)
      (coe
         MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (64 :: Integer)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim.du_riscv64'45'emitter_568)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim.du_riscv64'45'machine_594)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim.du_riscv64'45'traceloop_608
         (coe du_rv64'45'frame'45'semantics_38 (coe v2)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim.du_riscv64'45'supply_1868
         (coe v0) (coe du_rv64'45'frame'45'semantics_38 (coe v2)) (coe v8)
         (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.d_ret'45'no'45'wrap_132
            (coe v9))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.d_count'45'no'45'wrap_142
            (coe v9))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.d_lo'45'fits_152
            (coe v9))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.d_tag'45'fits_192
            (coe v10))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.d_lit'45'fits_204
            (coe v10))
         (\ v16 v17 v18 v19 v20 v21 v22 v23 ->
            coe
              MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.du_float'45'fits_218
              v20))
      (coe
         du_entry'45'view_2042
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'trace_146
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image_2138
               (coe v0) (coe v1) (coe v13))))
      (coe
         addInt (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2172
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_entry'45'vr_2312
               (coe v0) (coe v1) (coe du_rv64'45'frame'45'semantics_38 (coe v2))
               (coe
                  d_entry'45'frame'45'riscv64_1914 (coe v0) (coe v1) (coe v2)
                  (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                  (coe v10))
               (coe v13) (coe v14)
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_4770
                  (coe v0) (coe v1) (coe du_rv64'45'frame'45'semantics_38 (coe v2)))
               (coe v11) (coe (0 :: Integer)))))
      (coe MAlonzo.Code.Once.Adequacy.CPU.RiscV64.d_ev'45'riscv64_8)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.RiscV64.d_block'45'env_12
         (coe MAlonzo.Code.Once.Compile.d_blocks'45'riscv64_998 (coe v12)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_image_2138
         (coe v0) (coe v1) (coe v13))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs.du_start'45'flat_2274
         (coe
            d_entry'45'frame'45'riscv64_1914 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
            (coe v10)))
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_initState_454)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_878
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v13))
      (coe du_entry'45'corr_2066) (coe du_entry'45'wf_2112)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe du_entry'45'regtag_2136)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15) erased))
      (coe du_run'8320'_2196 (coe v1) (coe v13) (coe v14))
-- Once.Adequacy.ArchCorrectness.RiscV64.BlockRunsHyp-riscv64
d_BlockRunsHyp'45'riscv64_2200 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  ()
d_BlockRunsHyp'45'riscv64_2200 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.file-tr-riscv64
d_file'45'tr'45'riscv64_2218 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_file'45'tr'45'riscv64_2218 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 v19
  = du_file'45'tr'45'riscv64_2218
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v15 v19
du_file'45'tr'45'riscv64_2218 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_file'45'tr'45'riscv64_2218 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14
  = coe
      du_conc'45'tr_2180 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe du_p_2242 (coe v12) (coe v13))
      (coe du_ir'8242'_2244 (coe v12) (coe v13)) (coe v14)
-- Once.Adequacy.ArchCorrectness.RiscV64._.p
d_p_2242 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_p_2242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
         ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_p_2242 v12 v15
du_p_2242 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
du_p_2242 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_868 (coe v0)) (coe v1)
-- Once.Adequacy.ArchCorrectness.RiscV64._.ir′
d_ir'8242'_2244 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ir'8242'_2244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_ir'8242'_2244 v12 v15
du_ir'8242'_2244 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_ir'8242'_2244 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.d_main_388
      (coe
         MAlonzo.Code.Once.Compile.d_rewrite'45'program_894
         (coe du_p_2242 (coe v0) (coe v1)))
-- Once.Adequacy.ArchCorrectness.RiscV64._.img
d_img_2246 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_img_2246 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._._.img-at
d_img'45'at_2256 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_img'45'at_2256 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._.code-eq
d_code'45'eq_2258 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_422 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_156 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_2258 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._.Reachable
d_Reachable_30545 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  = ()
