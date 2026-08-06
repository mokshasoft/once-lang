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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Size
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.IRObsCorrectFlat.fits-erase
d_fits'45'erase_12 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
d_fits'45'erase_12 ~v0 ~v1 v2 = du_fits'45'erase_12 v2
du_fits'45'erase_12 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
du_fits'45'erase_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_fits'45'int_198
        -> coe MAlonzo.Code.Once.IRTy.C_fits'45'int_512
      MAlonzo.Code.Once.Type.C_fits'45'float_200
        -> coe MAlonzo.Code.Once.IRTy.C_fits'45'float_514
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat._.ir-to-trace
d_ir'45'to'45'trace_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286]
d_ir'45'to'45'trace_16 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat._.ClosureWellFormedDef.ResultPlace
d_ResultPlace_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_118 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat._.ClosureWellFormedDef.prim-sv
d_prim'45'sv_228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_prim'45'sv_228 ~v0 = du_prim'45'sv_228
du_prim'45'sv_228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_prim'45'sv_228 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_534
      v3 v4
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState
d_FlatState_646 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.fetch
d_fetch_712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
d_fetch_712 ~v0 ~v1 ~v2 = du_fetch_712
du_fetch_712 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
du_fetch_712 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_210
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.forced
d_forced_754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_forced_754 ~v0 ~v1 ~v2 = du_forced_754
du_forced_754 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_forced_754
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_1790
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.falloc
d_falloc_822 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_822 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.fclosure
d_fclosure_824 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_824 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.floc
d_floc_826 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_826 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.fpc
d_fpc_828 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_828 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.fret
d_fret_830 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_830 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.exec-sigop-halts
d_exec'45'sigop'45'halts_834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> Bool
d_exec'45'sigop'45'halts_834 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts_834
du_exec'45'sigop'45'halts_834 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 -> Bool
du_exec'45'sigop'45'halts_834 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_2780
      v2
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_838 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_exec'45'sigop'45'output'45'of_838 ~v0 v1 ~v2
  = du_exec'45'sigop'45'output'45'of_838 v1
du_exec'45'sigop'45'output'45'of_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_exec'45'sigop'45'output'45'of_838 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2754
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_pure'45'sigop'45'out'45'aux_840 ~v0 v1 ~v2
  = du_pure'45'sigop'45'out'45'aux_840 v1
du_pure'45'sigop'45'out'45'aux_840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_pure'45'sigop'45'out'45'aux_840 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2718
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_pure'45'sigop'45'out'45'val_842 ~v0 ~v1 ~v2
  = du_pure'45'sigop'45'out'45'val_842
du_pure'45'sigop'45'out'45'val_842 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_pure'45'sigop'45'out'45'val_842 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2702
      v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.BeforeFrontier
d_BeforeFrontier_852 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.ResultPlace
d_ResultPlace_864 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.ValidAtWF
d_ValidAtWF_866 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.prim-sv
d_prim'45'sv_872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_prim'45'sv_872 ~v0 ~v1 ~v2 = du_prim'45'sv_872
du_prim'45'sv_872 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_prim'45'sv_872 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_534
      v1 v2
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.event-of
d_event'45'of_914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_event'45'of_914 ~v0 ~v1 ~v2 = du_event'45'of_914
du_event'45'of_914 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_event'45'of_914
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_326
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.flat-events
d_flat'45'events_916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_916 ~v0 v1 ~v2 = du_flat'45'events_916 v1
du_flat'45'events_916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events_916 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_332 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.Readable
d_Readable_922 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.μ-layer-iso
d_μ'45'layer'45'iso_964 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542
d_μ'45'layer'45'iso_964 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_μ'45'layer'45'iso_964 v10
du_μ'45'layer'45'iso_964 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542
du_μ'45'layer'45'iso_964 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_890 v6 v8
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.flat-run
d_flat'45'run_982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'run_982 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_flat'45'run_982 v0 v1 v3 v4 v5 v6 v7 v8
du_flat'45'run_982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'run_982 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_1130 (coe v1)
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
         (coe v0) (coe v3) (coe v4) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_90 (coe v6)
         (coe v7) (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
            (coe (0 :: Integer))))
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.flat-run-keeps-next-slot
d_flat'45'run'45'keeps'45'next'45'slot_1004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'run'45'keeps'45'next'45'slot_1004 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.alg-run-keeps-frontier-0
d_alg'45'run'45'keeps'45'frontier'45'0_1026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alg'45'run'45'keeps'45'frontier'45'0_1026 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.MachineRefinesObsF
d_MachineRefinesObsF_1050 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_MachineRefinesObsF_1050
  = C_constructor_1092 (Integer ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.MachineRefinesObsF.traces-agree
d_traces'45'agree_1082 ::
  T_MachineRefinesObsF_1050 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_traces'45'agree_1082 v0
  = case coe v0 of
      C_constructor_1092 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.MachineRefinesObsF.value-realized
d_value'45'realized_1090 ::
  T_MachineRefinesObsF_1050 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_value'45'realized_1090 v0
  = case coe v0 of
      C_constructor_1092 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.InputAt
d_InputAt_1102 a0 a1 a2 a3 a4 a5 a6 = ()
data T_InputAt_1102
  = C_in'45'loc_1112 |
    C_in'45'reg_1116 MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 |
    C_in'45'unit_1118
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.IRObsCorrectF
d_IRObsCorrectF_1124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_1124 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.cata-correct
d_cata'45'correct_1150
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.cata-correct"
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.obs-correct-rest
d_obs'45'correct'45'rest_1158
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.obs-correct-rest"
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.sigop-halts-false
d_sigop'45'halts'45'false_1168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'halts'45'false_1168 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.sv-loc-of
d_sv'45'loc'45'of_1182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'loc'45'of_1182 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.pure-sigop-value-reg
d_pure'45'sigop'45'value'45'reg_1208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pure'45'sigop'45'value'45'reg_1208 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.step2
d_step2_1228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_1228 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.step2
d_step2_1266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_1266 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.pure-sigop-out-unit
d_pure'45'sigop'45'out'45'unit_1328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pure'45'sigop'45'out'45'unit_1328 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.pure-sigop-value-correct
d_pure'45'sigop'45'value'45'correct_1364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_1102 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pure'45'sigop'45'value'45'correct_1364 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.step2
d_step2_1434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_1434 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.step2
d_step2_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_1478 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.pure-obs-correct-sigop
d_pure'45'obs'45'correct'45'sigop_1596 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  T_InputAt_1102 -> T_MachineRefinesObsF_1050
d_pure'45'obs'45'correct'45'sigop_1596 v0 v1 ~v2 v3 v4 v5 v6 ~v7
                                       ~v8 ~v9 ~v10 ~v11 v12 v13 v14 ~v15 ~v16 v17 ~v18 ~v19
  = du_pure'45'obs'45'correct'45'sigop_1596
      v0 v1 v3 v4 v5 v6 v12 v13 v14 v17
du_pure'45'obs'45'correct'45'sigop_1596 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_MachineRefinesObsF_1050
du_pure'45'obs'45'correct'45'sigop_1596 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = coe
      C_constructor_1092
      (coe
         (\ v10 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (2 :: Integer))
              erased))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Once.IR.C_Stack_6)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe
                  MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82
                  (coe
                     du_flat'45'run_982 (coe v0) (coe v1) (coe (2 :: Integer))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                     (coe MAlonzo.Code.Once.IR.C_SigOp_154 (coe v2) (coe v3) (coe v4))
                     (coe v7) (coe v8)))
               (coe
                  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1006 v6
                  (coe du_fits'45'erase_12 (coe v5)) v9 v9))))
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.ev-[]
d_ev'45''91''93'_1638 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  T_InputAt_1102 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ev'45''91''93'_1638 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.mach-[]
d_mach'45''91''93'_1654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  T_InputAt_1102 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mach'45''91''93'_1654 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.denot-[]
d_denot'45''91''93'_1660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  T_InputAt_1102 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_1660 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.keeps-alloc
d_keeps'45'alloc_1668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  T_InputAt_1102 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'alloc_1668 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.before
d_before_1678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_752 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  T_InputAt_1102 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_before_1678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19
  = du_before_1678 v17
du_before_1678 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_before_1678 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.obs-correct-sigop
d_obs'45'correct'45'sigop_1692 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
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
  T_InputAt_1102 -> T_MachineRefinesObsF_1050
d_obs'45'correct'45'sigop_1692 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v4) in
    coe
      (let v7
             = coe
                 MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'63'_766
                 (coe v3) in
       coe
         (case coe v6 of
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
              -> case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                     -> let v10
                              = coe
                                  MAlonzo.Code.Once.SigOp.Info.du_go_224
                                  (coe MAlonzo.Code.Once.SigOp.Info.d_sem_176 (coe v5)) in
                        coe
                          (case coe v10 of
                             MAlonzo.Code.Once.SigOp.Info.C_Pure_124
                               -> coe
                                    (\ v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ->
                                       coe
                                         du_pure'45'obs'45'correct'45'sigop_1596 (coe v0) (coe v1)
                                         (coe v3) (coe v4) (coe v5) (coe v8) v14 v15 v16 v19)
                             MAlonzo.Code.Once.SigOp.Info.C_Emits_126
                               -> coe
                                    d_obs'45'correct'45'rest_1158 v0 v1 v2
                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v4))
                                    (coe
                                       MAlonzo.Code.Once.IR.C_SigOp_154 (coe v3) (coe v4) (coe v5))
                             MAlonzo.Code.Once.SigOp.Info.C_Halts_128
                               -> coe
                                    d_obs'45'correct'45'rest_1158 v0 v1 v2
                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v4))
                                    (coe
                                       MAlonzo.Code.Once.IR.C_SigOp_154 (coe v3) (coe v4) (coe v5))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          d_obs'45'correct'45'rest_1158 v0 v1 v2
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_SigOp_154 (coe v3) (coe v4) (coe v5))
                   _ -> MAlonzo.RTE.mazUnreachableError
            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
              -> coe
                   d_obs'45'correct'45'rest_1158 v0 v1 v2
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v4))
                   (coe MAlonzo.Code.Once.IR.C_SigOp_154 (coe v3) (coe v4) (coe v5))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-size-f
d_comp'45'size'45'f_1774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_comp'45'size'45'f_1774 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_comp'45'size'45'f_1774 v3 v4 v5 v6 v7 v8
du_comp'45'size'45'f_1774 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_comp'45'size'45'f_1774 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
            (coe
               MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v0) (coe v1)
               (coe v4)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               addInt
               (coe
                  MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v0) (coe v1)
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v1) (coe v2)
                  (coe v3)))))
      (coe v5)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-size-g
d_comp'45'size'45'g_1792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_comp'45'size'45'g_1792 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_comp'45'size'45'g_1792 v3 v4 v5 v6 v7 v8
du_comp'45'size'45'g_1792 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_comp'45'size'45'g_1792 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v1) (coe v2)
               (coe v3)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               addInt
               (coe
                  MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v0) (coe v1)
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v1) (coe v2)
                  (coe v3)))))
      (coe v5)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-step
d_comp'45'step_1816
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-step"
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-obs-correct
d_comp'45'obs'45'correct_1828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_InputAt_1102 -> T_MachineRefinesObsF_1050) ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_542 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_InputAt_1102 -> T_MachineRefinesObsF_1050) ->
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
  T_InputAt_1102 -> T_MachineRefinesObsF_1050
d_comp'45'obs'45'correct_1828 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14 v15 v16 v17 v18 v19 v20
  = coe
      d_comp'45'step_1816 v0 v1 v2 v3 v4 v5 v6 v7 v12 v14 v15
      (coe
         du_comp'45'size'45'g_1792 (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v10))
      v8
      (coe
         v9
         (coe
            du_comp'45'size'45'f_1774 (coe v3) (coe v4) (coe v5) (coe v6)
            (coe v7) (coe v10))
         v11 v12 v13 v14 v15 v16 v17 v18 v19 v20)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.ir-obs-correct
d_ir'45'obs'45'correct_1866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  T_InputAt_1102 -> T_MachineRefinesObsF_1050
d_ir'45'obs'45'correct_1866 v0 v1 v2 v3 v4 v5
  = let v6 = coe d_obs'45'correct'45'rest_1158 v0 v1 v2 v3 v4 v5 in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.IR.C__'8728'__30 v8 v10 v11
           -> coe
                d_comp'45'obs'45'correct_1828 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v8) (coe v4) (coe v10) (coe v11)
                (coe
                   d_ir'45'obs'45'correct_1866 (coe v0) (coe v1) (coe v2) (coe v8)
                   (coe v4) (coe v10))
                (coe
                   d_ir'45'obs'45'correct_1866 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v8) (coe v11))
         MAlonzo.Code.Once.IR.C_Cata_106 v8 v10
           -> case coe v3 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v11
                  -> coe
                       d_cata'45'correct_1150 v0 v1 v2 v11 v8 v4 v10
                       (d_ir'45'obs'45'correct_1866
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v11) (coe v4))
                          (coe v4) (coe v10))
                _ -> coe v6
         MAlonzo.Code.Once.IR.C_SigOp_154 v7 v8 v9
           -> coe
                d_obs'45'correct'45'sigop_1692 (coe v0) (coe v1) (coe v2) (coe v7)
                (coe v8) (coe v9)
         _ -> coe v6)
