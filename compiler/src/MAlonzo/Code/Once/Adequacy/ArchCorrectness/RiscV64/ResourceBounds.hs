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
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.CanonicalName

-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.HeapRoom
d_HeapRoom_12 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_HeapRoom_12 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.StackRoom
d_StackRoom_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_StackRoom_24 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.CallRoom
d_CallRoom_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_CallRoom_38 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.SlotAddrNoWrap
d_SlotAddrNoWrap_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_SlotAddrNoWrap_48 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.RegRange
d_RegRange_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_RegRange_60 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.ScratchDecGuarded
d_ScratchDecGuarded_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_ScratchDecGuarded_72 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.AddrNoWrap
d_AddrNoWrap_82 a0 = ()
data T_AddrNoWrap_82
  = C_constructor_148 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.AddrNoWrap.ret-no-wrap
d_ret'45'no'45'wrap_126 ::
  T_AddrNoWrap_82 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ret'45'no'45'wrap_126 v0
  = case coe v0 of
      C_constructor_148 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.AddrNoWrap.count-no-wrap
d_count'45'no'45'wrap_136 ::
  T_AddrNoWrap_82 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_count'45'no'45'wrap_136 v0
  = case coe v0 of
      C_constructor_148 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.AddrNoWrap.lo-fits
d_lo'45'fits_146 ::
  T_AddrNoWrap_82 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'fits_146 v0
  = case coe v0 of
      C_constructor_148 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.LitFits
d_LitFits_150 a0 = ()
data T_LitFits_150
  = C_constructor_224 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
                       Integer ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
                       MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.LitFits.tag-fits
d_tag'45'fits_198 ::
  T_LitFits_150 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tag'45'fits_198 v0
  = case coe v0 of
      C_constructor_224 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.LitFits.lit-fits
d_lit'45'fits_210 ::
  T_LitFits_150 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'fits_210 v0
  = case coe v0 of
      C_constructor_224 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds.LitFits.float-fits
d_float'45'fits_222 ::
  T_LitFits_150 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_float'45'fits_222 v0
  = case coe v0 of
      C_constructor_224 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
