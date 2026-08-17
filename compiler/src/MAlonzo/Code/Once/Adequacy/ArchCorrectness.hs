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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.Adequacy.ArchCorrectness.arch-correctness
d_arch'45'correctness_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_348 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_AddrNoWrap_202 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds.T_LitFits_270 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   Integer ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_AddrNoWrap_82 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.T_LitFits_150 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
d_arch'45'correctness_54 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13 v14 v15 v16 v17
  = case coe v17 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.d_x86'45'64'45'correct_530
             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe v7) (coe v8)
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z32.d_x86'45'32'45'correct_200
             (coe v0) (coe v1)
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.d_riscv64'45'correct_506
             (coe v0) (coe v1) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
             (coe v14) (coe v15) (coe v16)
      _ -> MAlonzo.RTE.mazUnreachableError
