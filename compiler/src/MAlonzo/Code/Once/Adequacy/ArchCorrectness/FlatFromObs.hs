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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatFromObs where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.IRObsCorrectF
d_IRObsCorrectF_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_24 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.InputAt
d_InputAt_26 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF
d_MachineRefinesObsF_28 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                        a13
  = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF.traces-agree
d_traces'45'agree_132 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_traces'45'agree_132 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_traces'45'agree_1156
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectFlatness.MachineRefinesObsF.value-realized
d_value'45'realized_134 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_value'45'realized_134 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_value'45'realized_1164
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ir-stack-budget
d_ir'45'stack'45'budget_138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_138 v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_ir'45'stack'45'budget_138 v0
du_ir'45'stack'45'budget_138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_138 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_750
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_196 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.IRObsCorrectF
d_IRObsCorrectF_716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_716 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF
d_MachineRefinesObsF_718 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF.traces-agree
d_traces'45'agree_726 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_traces'45'agree_726 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_traces'45'agree_1156
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.MachineRefinesObsF.value-realized
d_value'45'realized_728 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_value'45'realized_728 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_value'45'realized_1164
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.BeforeFrontier
d_BeforeFrontier_740 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.ValidAtWF
d_ValidAtWF_754 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.Adequacy.ArchCorrectness.FlatFromObs.asm-sem
d_asm'45'sem_782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_asm'45'sem_782 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_asm'45'sem_782 v4 v6
du_asm'45'sem_782 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_asm'45'sem_782 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_exec'45'bytes_40
      (coe v0)
      (coe MAlonzo.Code.Once.Adequacy.CPU.Interface.d_assemble_38 v0 v1)
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-size
d_entry'45'size_788
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatFromObs.entry-size"
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-alloc
d_entry'45'alloc_790 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_entry'45'alloc_790 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_entry'45'alloc_790 v3 v6
du_entry'45'alloc_790 ::
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_entry'45'alloc_790 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
      (coe (0 :: Integer)) (coe (1 :: Integer))
      (coe (\ v2 -> 0 :: Integer))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-loc
d_entry'45'loc_796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_entry'45'loc_796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_entry'45'loc_796
du_entry'45'loc_796 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_entry'45'loc_796
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe (0 :: Integer)))
         (coe (0 :: Integer)))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-regs
d_entry'45'regs_798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126
d_entry'45'regs_798 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_entry'45'regs_798
du_entry'45'regs_798 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_126
du_entry'45'regs_798
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkRegs_150
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
         (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
         (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
         (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
         (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
         (coe (0 :: Integer)))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-s
d_entry'45's_800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_entry'45's_800 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_entry'45's_800
du_entry'45's_800 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_entry'45's_800
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
      (coe du_entry'45'regs_798)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-ns
d_entry'45'ns_810 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'ns_810 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-bf
d_entry'45'bf_814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_entry'45'bf_814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_entry'45'bf_814
du_entry'45'bf_814 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_entry'45'bf_814
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_668
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-nh
d_entry'45'nh_816 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'nh_816 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.entry-witness
d_entry'45'witness_820 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1176 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124) ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124
d_entry'45'witness_820 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      v7 (coe d_entry'45'size_788 v0 v1 v2 v3 v4 v5 v6)
      (coe MAlonzo.Code.Once.IR.C_Stack_6)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe du_entry'45'loc_796) (coe du_entry'45's_800)
      (coe
         du_entry'45'alloc_790 (coe v3)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_750
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v6)))
      erased
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_778)
      (coe du_entry'45'bf_814) erased
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.C_in'45'unit_1192)
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-trace-of
d_flat'45'trace'45'of_832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1176 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'trace'45'of_832 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe
             MAlonzo.Code.Data.List.Base.du_take_530 (coe v8)
             (coe
                MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_360 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_traces'45'agree_1156
                      (d_entry'45'witness_820
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v9)
                         (coe
                            v6 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v9))
                      v8))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_732
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
                   (coe du_entry'45's_800)
                   (coe
                      du_entry'45'alloc_790 (coe v3)
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_750
                         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v9)))
                   (coe (0 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
                      (coe (0 :: Integer)))
                   (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatFromObs.AsmTraceCorrect
d_AsmTraceCorrect_842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
   Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  ()
d_AsmTraceCorrect_842 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.ir-flat-correct-of
d_ir'45'flat'45'correct'45'of_864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1176 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct'45'of_864 = erased
-- Once.Adequacy.ArchCorrectness.FlatFromObs.flat-from-obs
d_flat'45'from'45'obs_884 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1176 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124) ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
d_flat'45'from'45'obs_884 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_flat'45'from'45'obs_884 v0 v1 v2 v3 v4 v5 v6
du_flat'45'from'45'obs_884 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10 ->
  Integer ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_InputAt_1176 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_1124) ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
du_flat'45'from'45'obs_884 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.Compile.C_constructor_104
      (coe du_asm'45'sem_782 (coe v4))
      (d_flat'45'trace'45'of_832
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Adequacy.ArchCorrectness.FlatFromObs._.InputAt
d_InputAt_8769 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
