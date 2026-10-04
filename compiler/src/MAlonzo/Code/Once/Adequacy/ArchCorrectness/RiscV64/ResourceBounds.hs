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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds where

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
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic

-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.rv64-frame-semantics
d_rv64'45'frame'45'semantics_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
d_rv64'45'frame'45'semantics_14 ~v0 v1
  = du_rv64'45'frame'45'semantics_14 v1
du_rv64'45'frame'45'semantics_14 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
du_rv64'45'frame'45'semantics_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_308
      (coe v0)
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.HeapRoom
d_HeapRoom_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_HeapRoom_16 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.StackRoom
d_StackRoom_28 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_StackRoom_28 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.CallRoom
d_CallRoom_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_CallRoom_42 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.SlotAddrNoWrap
d_SlotAddrNoWrap_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_SlotAddrNoWrap_54 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.RegRange
d_RegRange_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_RegRange_66 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.ScratchDecGuarded
d_ScratchDecGuarded_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 -> ()
d_ScratchDecGuarded_78 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.AddrNoWrap
d_AddrNoWrap_88 a0 a1 = ()
data T_AddrNoWrap_88
  = C_constructor_154 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.AddrNoWrap.ret-no-wrap
d_ret'45'no'45'wrap_132 ::
  T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ret'45'no'45'wrap_132 v0
  = case coe v0 of
      C_constructor_154 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.AddrNoWrap.count-no-wrap
d_count'45'no'45'wrap_142 ::
  T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_count'45'no'45'wrap_142 v0
  = case coe v0 of
      C_constructor_154 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.AddrNoWrap.lo-fits
d_lo'45'fits_152 ::
  T_AddrNoWrap_88 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'fits_152 v0
  = case coe v0 of
      C_constructor_154 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.LitFits
d_LitFits_156 a0 a1 = ()
data T_LitFits_156
  = C_constructor_206 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.LitFits.tag-fits
d_tag'45'fits_192 ::
  T_LitFits_156 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tag'45'fits_192 v0
  = case coe v0 of
      C_constructor_206 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.LitFits.lit-fits
d_lit'45'fits_204 ::
  T_LitFits_156 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'fits_204 v0
  = case coe v0 of
      C_constructor_206 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.float-fits
d_float'45'fits_218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_414 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_float'45'fits_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_float'45'fits_218 v6
du_float'45'fits_218 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_float'45'fits_218 v0
  = coe
      MAlonzo.Code.Once.Float.Decimal.d_round'45'fits_302
      (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42) (coe v0)
