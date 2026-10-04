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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.SigOp where

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
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Prelude
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Σ
d_Σ_11 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractReg
d_AbstractReg_13 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Bool
d_Bool_17 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.fits-erase
d_fits'45'erase_18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518
d_fits'45'erase_18 ~v0 ~v1 = du_fits'45'erase_18
du_fits'45'erase_18 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518
du_fits'45'erase_18 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Prelude.du_fits'45'erase_16
      v1
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.⊤
d_'8868'_19 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.FlatState
d_FlatState_754 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.FlatSteps
d_FlatSteps_758 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.IRObsCorrectF
d_IRObsCorrectF_770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_770 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.InputAt
d_InputAt_774 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.MachineRefinesObsF
d_MachineRefinesObsF_780 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.Readable
d_Readable_786 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ResultPlace
d_ResultPlace_788 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.SpanAt
d_SpanAt_792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_SpanAt_792 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized
d_ValueRealized_800 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.emitted
d_emitted_874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_emitted_874 v0 ~v1 = du_emitted_874 v0
du_emitted_874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_emitted_874 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_3464
      (coe v0) v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.evalᴰ
d_eval'7472'_892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_892 ~v0 v1 = du_eval'7472'_892 v1
du_eval'7472'_892 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_892 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_2658
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.exec-sigop-halts
d_exec'45'sigop'45'halts_938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_938 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts_938
du_exec'45'sigop'45'halts_938 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts_938 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_3126
      v2
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_940 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts'45'of_940
du_exec'45'sigop'45'halts'45'of_940 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts'45'of_940 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_3120
      v2
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_942 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_942 ~v0 ~v1 v2
  = du_exec'45'sigop'45'output'45'of_942 v2
du_exec'45'sigop'45'output'45'of_942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_942 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_3068
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.prim-sv
d_prim'45'sv_1128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_1128 ~v0 ~v1 ~v2 = du_prim'45'sv_1128
du_prim'45'sv_1128 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_1128 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_582
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_1130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_1130 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'aux_1130 v2
du_pure'45'sigop'45'out'45'aux_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'aux_1130 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_3032
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_1132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_1132 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'val_1132 v2
du_pure'45'sigop'45'out'45'val_1132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_1132 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'val_3008
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.pure-sigop-output
d_pure'45'sigop'45'output_1134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_1134 ~v0 ~v1 v2
  = du_pure'45'sigop'45'output_1134 v2
du_pure'45'sigop'45'output_1134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'output_1134 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_3002
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.readTyped
d_readTyped_1156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_readTyped_1156 ~v0 ~v1 ~v2 = du_readTyped_1156
du_readTyped_1156 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_readTyped_1156
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2818
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.FlatState.falloc
d_falloc_1368 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_1368 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.FlatState.fclosure
d_fclosure_1370 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1370 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.FlatState.flink
d_flink_1372 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1372 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.FlatState.floc
d_floc_1374 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_1374 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.FlatState.fpc
d_fpc_1376 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1376 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.FlatState.fret
d_fret_1378 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1378 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.MachineRefinesObsF.traces-agree
d_traces'45'agree_1414 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1414 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.MachineRefinesObsF.value-realized
d_value'45'realized_1416 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600
d_value'45'realized_1416 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3814
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.at-end
d_at'45'end_1478 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1478 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.bf-mono
d_bf'45'mono_1480 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_1480 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.cont-alloc
d_cont'45'alloc_1482 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_1482 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.frame-pres
d_frame'45'pres_1484 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1484 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.heap-pres
d_heap'45'pres_1486 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_1486 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.live
d_live_1488 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1488 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.log
d_log_1490 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1490 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.no-link
d_no'45'link_1492 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1492 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.no-ret
d_no'45'ret_1494 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1494 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.out-mode
d_out'45'mode_1496 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1496 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.place
d_place_1498 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_1498 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3694
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.run
d_run_1500 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_1500 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.settle
d_settle_1502 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1502 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.stack-pres
d_stack'45'pres_1504 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_1504 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.steps
d_steps_1506 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_steps_1506 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3670
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Core.ValueRealized.stops
d_stops_1508 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_1508 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_1512 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._._×_
d__'215'__1954 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'__1954 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._._≡_
d__'8801'__1964 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractInstr
d_AbstractInstr_1990 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractTrace
d_AbstractTrace_1992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> ()
d_AbstractTrace_1992 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AllocMode
d_AllocMode_1996 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AllocState
d_AllocState_1998 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.EffectShape
d_EffectShape_2018 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FitsInReg
d_FitsInReg_2022 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FitsInRegI
d_FitsInRegI_2024 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics
d_FrameSemantics_2026 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.IR
d_IR_2042 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.LocState
d_LocState_2058 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Maybe
d_Maybe_2062 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.SigOpInfo
d_SigOpInfo_2084 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.StoredValue
d_StoredValue_2090 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Type
d_Type_2092 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.ValueLocation
d_ValueLocation_2098 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.fst
d_fst_2216 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_2216 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.snd
d_snd_2218 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_2218 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.readReg
d_readReg_2220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readReg_2220 ~v0 ~v1 = du_readReg_2220
du_readReg_2220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readReg_2220 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.subst
d_subst_2240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_subst_2240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_subst_2240 v9
du_subst_2240 :: AgdaAny -> AgdaAny
du_subst_2240 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.sv-as-loc
d_sv'45'as'45'loc_2250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_2250 ~v0 ~v1 = du_sv'45'as'45'loc_2250
du_sv'45'as'45'loc_2250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_2250 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370 v1
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.sym
d_sym_2252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2252 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.Nat
d_Nat_2278 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.⊥
d_'8869'_2294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> ()
d_'8869'_2294 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.⌊_⌋
d_'8970'_'8971'_2298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_'8970'_'8971'_2298 ~v0 ~v1 = du_'8970'_'8971'_2298
du_'8970'_'8971'_2298 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
du_'8970'_'8971'_2298
  = coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_2302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_2302 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractExec.call-sigop-output
d_call'45'sigop'45'output_2330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'output_2330 ~v0 ~v1
  = du_call'45'sigop'45'output_2330
du_call'45'sigop'45'output_2330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_call'45'sigop'45'output_2330
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'output_2990
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractExec.call-sigop-val
d_call'45'sigop'45'val_2332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'val_2332 ~v0 ~v1 = du_call'45'sigop'45'val_2332
du_call'45'sigop'45'val_2332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_call'45'sigop'45'val_2332
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'val_2974
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractExec.decode-at
d_decode'45'at_2338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_decode'45'at_2338 ~v0 ~v1 = du_decode'45'at_2338
du_decode'45'at_2338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_decode'45'at_2338 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_decode'45'at_2868 v1 v2 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_2368 ~v0 ~v1
  = du_exec'45'sigop'45'output_2368
du_exec'45'sigop'45'output_2368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output_2368
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_3110
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractExec.machine-events
d_machine'45'events_2406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_machine'45'events_2406 ~v0 ~v1 = du_machine'45'events_2406
du_machine'45'events_2406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_machine'45'events_2406 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_machine'45'events_2898 v1
      v3 v4
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractExec.sigop-events
d_sigop'45'events_2430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events_2430 ~v0 ~v1 = du_sigop'45'events_2430
du_sigop'45'events_2430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events_2430 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sigop'45'events_3100 v1 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AbstractExec.sigop-events-of
d_sigop'45'events'45'of_2432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events'45'of_2432 ~v0 ~v1
  = du_sigop'45'events'45'of_2432
du_sigop'45'events'45'of_2432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events'45'of_2432 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sigop'45'events'45'of_3082
      v1 v3 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AllocState.block-size
d_block'45'size_2516 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> Integer
d_block'45'size_2516 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_594 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AllocState.current-frame
d_current'45'frame_2518 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> AgdaAny
d_current'45'frame_2518 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AllocState.frame-slots
d_frame'45'slots_2520 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_frame'45'slots_2520 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_588 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AllocState.next-heap-ref
d_next'45'heap'45'ref_2522 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'heap'45'ref_2522 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AllocState.next-slot
d_next'45'slot_2524 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'slot_2524 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_590 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.AllocState.saved-frames
d_saved'45'frames_2526 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_2526 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_586 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics._≟F_
d__'8799'F__3026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__3026 v0
  = coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics._≺_
d__'8826'__3028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> ()
d__'8826'__3028 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.Frame
d_Frame_3030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_Frame_3030 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.float-format
d_float'45'format_3032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_3032 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.frame-base
d_frame'45'base_3034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
d_frame'45'base_3034 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_3036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_3036 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.frame-word
d_frame'45'word_3038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_frame'45'word_3038 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_110 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_3040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_3040 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word'45'pos_112
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.fs-interp
d_fs'45'interp_3042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_fs'45'interp_3042 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.shift-base
d_shift'45'base_3044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_3044 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.shift-frame
d_shift'45'frame_3046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_3046 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_108 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.slot-addr
d_slot'45'addr_3048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_3048 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_94 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_3050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_3050 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.slot-injective
d_slot'45'injective_3052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_3052 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_3054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_3054 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.≺-compare
d_'8826''45'compare_3056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_3056 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'compare_148
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_3058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_3058 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.FrameSemantics.≺-trans
d_'8826''45'trans_3060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_3060 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_138 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.LocState.ev-log
d_ev'45'log_3262 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_ev'45'log_3262 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.LocState.halted
d_halted_3264 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_halted_3264 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_422 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.LocState.heapMem
d_heapMem_3266 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_heapMem_3266 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_420 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.LocState.regs
d_regs_3268 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs_3268 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.LocState.stackMem
d_stackMem_3270 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_stackMem_3270 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_418 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.SigOpInfo.baseA
d_baseA_3498 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_baseA_3498 v0
  = coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.SigOpInfo.conB
d_conB_3500 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_conB_3500 v0
  = coe MAlonzo.Code.Once.SigOp.Info.d_conB_184 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.SigOpInfo.name
d_name_3502 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_name_3502 v0
  = coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp._.SigOpInfo.sem
d_sem_3504 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142
d_sem_3504 v0 = coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.FlatState
d_FlatState_3788 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.FlatSteps
d_FlatSteps_3792 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.IRObsCorrectF
d_IRObsCorrectF_3804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_3804 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.InputAt
d_InputAt_3808 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.MachineRefinesObsF
d_MachineRefinesObsF_3814 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.Readable
d_Readable_3820 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ResultPlace
d_ResultPlace_3822 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.SpanAt
d_SpanAt_3826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_SpanAt_3826 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized
d_ValueRealized_3834 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.emitted
d_emitted_3908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_emitted_3908 v0 ~v1 ~v2 = du_emitted_3908 v0
du_emitted_3908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_emitted_3908 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_3464
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.evalᴰ
d_eval'7472'_3926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_3926 ~v0 v1 v2 = du_eval'7472'_3926 v1 v2
du_eval'7472'_3926 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_3926 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_2658
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.exec-sigop-halts
d_exec'45'sigop'45'halts_3972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_3972 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts_3972
du_exec'45'sigop'45'halts_3972 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts_3972 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_3126
      v2
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_3974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_3974 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts'45'of_3974
du_exec'45'sigop'45'halts'45'of_3974 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts'45'of_3974 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_3120
      v2
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_3976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_3976 ~v0 ~v1 v2
  = du_exec'45'sigop'45'output'45'of_3976 v2
du_exec'45'sigop'45'output'45'of_3976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_3976 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_3068
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.prim-sv
d_prim'45'sv_4162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_4162 ~v0 ~v1 ~v2 = du_prim'45'sv_4162
du_prim'45'sv_4162 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_4162 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_582
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_4164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_4164 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'aux_4164 v2
du_pure'45'sigop'45'out'45'aux_4164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'aux_4164 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_3032
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_4166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_4166 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'val_4166 v2
du_pure'45'sigop'45'out'45'val_4166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_4166 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'val_3008
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.pure-sigop-output
d_pure'45'sigop'45'output_4168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_4168 ~v0 ~v1 v2
  = du_pure'45'sigop'45'output_4168 v2
du_pure'45'sigop'45'output_4168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'output_4168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_3002
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.readTyped
d_readTyped_4190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_readTyped_4190 ~v0 ~v1 ~v2 = du_readTyped_4190
du_readTyped_4190 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_readTyped_4190
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2818
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.FlatState.falloc
d_falloc_4402 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_4402 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.FlatState.fclosure
d_fclosure_4404 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_4404 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.FlatState.flink
d_flink_4406 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_4406 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.FlatState.floc
d_floc_4408 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_4408 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.FlatState.fpc
d_fpc_4410 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_4410 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.FlatState.fret
d_fret_4412 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_4412 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.MachineRefinesObsF.traces-agree
d_traces'45'agree_4448 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_4448 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.MachineRefinesObsF.value-realized
d_value'45'realized_4450 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600
d_value'45'realized_4450 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3814
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.at-end
d_at'45'end_4512 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_4512 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.bf-mono
d_bf'45'mono_4514 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_4514 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.cont-alloc
d_cont'45'alloc_4516 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_4516 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.frame-pres
d_frame'45'pres_4518 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_4518 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.heap-pres
d_heap'45'pres_4520 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_4520 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.live
d_live_4522 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_4522 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.log
d_log_4524 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_4524 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.no-link
d_no'45'link_4526 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_4526 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.no-ret
d_no'45'ret_4528 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_4528 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.out-mode
d_out'45'mode_4530 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_4530 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.place
d_place_4532 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_4532 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3694
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.run
d_run_4534 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_4534 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.settle
d_settle_4536 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_4536 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.stack-pres
d_stack'45'pres_4538 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_4538 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.steps
d_steps_4540 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_steps_4540 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3670
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ValueRealized.stops
d_stops_4542 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_4542 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_4546 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.call-sigop-output
d_call'45'sigop'45'output_4988 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'output_4988 ~v0 ~v1 v2
  = du_call'45'sigop'45'output_4988 v2
du_call'45'sigop'45'output_4988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_call'45'sigop'45'output_4988 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'output_2990
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.call-sigop-val
d_call'45'sigop'45'val_4990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'val_4990 ~v0 ~v1 v2
  = du_call'45'sigop'45'val_4990 v2
du_call'45'sigop'45'val_4990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_call'45'sigop'45'val_4990 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'val_2974
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.decode-at
d_decode'45'at_4992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_decode'45'at_4992 ~v0 ~v1 ~v2 = du_decode'45'at_4992
du_decode'45'at_4992 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_decode'45'at_4992
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_decode'45'at_2868
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.exec-sigop-output
d_exec'45'sigop'45'output_4996 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_4996 ~v0 ~v1 v2
  = du_exec'45'sigop'45'output_4996 v2
du_exec'45'sigop'45'output_4996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output_4996 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_3110
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.machine-events
d_machine'45'events_4998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_machine'45'events_4998 ~v0 ~v1 ~v2 = du_machine'45'events_4998
du_machine'45'events_4998 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_machine'45'events_4998 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_machine'45'events_2898 v0
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.sigop-events
d_sigop'45'events_5002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events_5002 ~v0 ~v1 ~v2 = du_sigop'45'events_5002
du_sigop'45'events_5002 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events_5002 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sigop'45'events_3100 v0 v2
      v3
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.sigop-events-of
d_sigop'45'events'45'of_5004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events'45'of_5004 ~v0 ~v1 ~v2
  = du_sigop'45'events'45'of_5004
du_sigop'45'events'45'of_5004 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events'45'of_5004 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sigop'45'events'45'of_3082
      v0 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.fmt
d_fmt_5006 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14
d_fmt_5006 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.φ
d_φ_5008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_φ_5008 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_540
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.σᶠ
d_σ'7584'_5010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_σ'7584'_5010 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.d_sig_464
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.argOf
d_argOf_5016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> AgdaAny -> AgdaAny
d_argOf_5016 ~v0 v1 ~v2 v3 v4 = du_argOf_5016 v1 v3 v4
du_argOf_5016 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> AgdaAny -> AgdaAny
du_argOf_5016 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_356
      (coe v0) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v1))
      (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.resOf
d_resOf_5028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> AgdaAny -> AgdaAny
d_resOf_5028 ~v0 ~v1 v2 v3 v4 = du_resOf_5028 v2 v3 v4
du_resOf_5028 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> AgdaAny -> AgdaAny
du_resOf_5028 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_386
      (coe v0) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_184 (coe v1))
      (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.evalᴰ-at
d_eval'7472''45'at_5046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'at_5046 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.events-at
d_events'45'at_5068 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events'45'at_5068 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.output-at
d_output'45'at_5090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'at_5090 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.halts-at
d_halts'45'at_5112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halts'45'at_5112 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.decode-ptr
d_decode'45'ptr_5132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decode'45'ptr_5132 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.arg-reg
d_arg'45'reg_5144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'reg_5144 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.arg-agree
d_arg'45'agree_5208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'agree_5208 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.event-agree
d_event'45'agree_5280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_event'45'agree_5280 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.Step.E
d_E_5320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_E_5320 ~v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13 ~v14
         ~v15
  = du_E_5320 v1 v2 v3 v4 v5 v11
du_E_5320 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_E_5320 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_2658
      v0 v1 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
      (coe MAlonzo.Code.Once.IR.C_SigOp_130 (coe v2) (coe v3) (coe v4))
      v5
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.Step.fs₁
d_fs'8321'_5322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5322 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 v12 ~v13
  = du_fs'8321'_5322 v0 v1 v2 v3 v7 v10 v11 v12
du_fs'8321'_5322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5322 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 (coe v1)
         (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v5)
         (coe v6) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v7)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.Step.build
d_build_5330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_build_5330 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 ~v11 v12 v13
             v14 v15 ~v16 ~v17 ~v18 v19 ~v20
  = du_build_5330 v2 v3 v4 v5 v9 v10 v12 v13 v14 v15 v19
du_build_5330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_build_5330 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3818
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3714
         (1 :: Integer)
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
            (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 (coe v1)
               (coe v2) (coe v3))
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v6)
               (coe v7) (coe v4)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v8)
               (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
         (coe MAlonzo.Code.Once.IR.C_Stack_6)
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
               (coe v0)
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 (coe v1)
                  (coe v2) (coe v3))
               (coe v6) (coe v7)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 (coe v1)
               (coe v2) (coe v3))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
               (coe
                  v5 (0 :: Integer)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 (coe v1)
                     (coe v2) (coe v3))
                  erased))
            (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
         v10 (\ v11 v12 v13 -> v13))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.res-reg
d_res'45'reg_5370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_res'45'reg_5370 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.forget-reg
d_forget'45'reg_5380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'reg_5380 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.forget-reg-float
d_forget'45'reg'45'float_5388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'reg'45'float_5388 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.pure-input-aux
d_pure'45'input'45'aux_5410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pure'45'input'45'aux_5410 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.pure-sigop-out-unit-any
d_pure'45'sigop'45'out'45'unit'45'any_5464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pure'45'sigop'45'out'45'unit'45'any_5464 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.pure-input
d_pure'45'input_5568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pure'45'input_5568 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.pure-agree
d_pure'45'agree_5602 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pure'45'agree_5602 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9
  = du_pure'45'agree_5602 v2 v3 v4 v5 v6 v9
du_pure'45'agree_5602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pure'45'agree_5602 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.SigOp.Info.C_pureV_148 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92 (coe v2)
                (coe
                   v6
                   (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166
                      (coe v0))
                   v5))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.SigOp.Info.C_ffiV_150
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonad.d_pure_496
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
                (coe du_k_5630 (coe v1) (coe v2) (coe v3))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_y_5632 (coe v0) (coe v1) (coe v2) (coe v3)))
                v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.SigOp.Info.C_primV_158 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92 (coe v2)
                (coe
                   MAlonzo.Code.Once.Arith.Prim.du_primSem_392 v6
                   (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166
                      (coe v0))
                   v5))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.k
d_k_5630 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Contract.T_Key_124
d_k_5630 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 = du_k_5630 v3 v4 v5
du_k_5630 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Spec.Contract.T_Key_124
du_k_5630 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Contract.C_key_138
      (coe
         MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
         (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v2)))
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.y
d_y_5632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_y_5632 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 = du_y_5632 v2 v3 v4 v5
du_y_5632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_y_5632 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Contract.du_yes'45'of_184
      (coe
         MAlonzo.Code.Once.Spec.Contract.C_key_138
         (coe
            MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
            (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v3)))
         (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.Spec.Contract.d_valueKeys_298
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.d_sig_464
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.pure-obs
d_pure'45'obs_5658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_pure'45'obs_5658 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                   ~v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 v24 v25
                   ~v26 ~v27 ~v28
  = du_pure'45'obs_5658 v2 v3 v4 v5 v10 v15 v23 v24 v25
du_pure'45'obs_5658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_pure'45'obs_5658 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_build_5330 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) erased
      (coe v6) (coe v7) (coe v8) erased
      (\ v10 v11 -> coe du_place_5736 (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.E
d_E_5708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_E_5708 ~v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25 ~v26
         ~v27 ~v28
  = du_E_5708 v1 v2 v3 v4 v5 v22
du_E_5708 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_E_5708 v0 v1 v2 v3 v4 v5
  = coe
      du_E_5320 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.build
d_build_5710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_build_5710 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 v24 v25 ~v26
             ~v27 ~v28
  = du_build_5710 v2 v3 v4 v5 v15 v23 v24 v25
du_build_5710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_build_5710 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_build_5330 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) erased
      (coe v5) (coe v6) (coe v7) erased v11
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.fs₁
d_fs'8321'_5712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5712 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
                v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 v22 v23 ~v24 ~v25 ~v26
  = du_fs'8321'_5712 v0 v1 v2 v3 v13 v21 v22 v23
du_fs'8321'_5712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5712 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 (coe v1)
         (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v5)
         (coe v6) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v7)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.a
d_a_5714 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  AgdaAny
d_a_5714 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25 ~v26
         ~v27 ~v28
  = du_a_5714 v3 v5 v22
du_a_5714 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> AgdaAny -> AgdaAny
du_a_5714 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_356
      (coe v0) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v1))
      (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.w
d_w_5716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  AgdaAny
d_w_5716 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25 ~v26
         ~v27 ~v28
  = du_w_5716 v2 v3 v4 v5 v6 v22
du_w_5716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 -> AgdaAny -> AgdaAny
du_w_5716 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_pure'45'agree_5602 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe du_a_5714 (coe v1) (coe v3) (coe v5)))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.E≡
d_E'8801'_5718 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E'8801'_5718 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ev-eq
d_ev'45'eq_5720 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ev'45'eq_5720 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.stops-f
d_stops'45'f_5724 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops'45'f_5724 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.out≡
d_out'8801'_5726 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'8801'_5726 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.place
d_place_5736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_5736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
             ~v26 ~v27 ~v28 ~v29 ~v30
  = du_place_5736 v10
du_place_5736 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
du_place_5736 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1092
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Prelude.du_fits'45'erase_16
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.emits-obs
d_emits'45'obs_5752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_emits'45'obs_5752 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                    ~v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 ~v20 ~v21 ~v22
  = du_emits'45'obs_5752 v2 v3 v4 v9 v17 v18 v19
du_emits'45'obs_5752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_emits'45'obs_5752 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_build_5330 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v2) (coe v3) erased
      (coe v4) (coe v5) (coe v6) erased
      (coe
         (\ v8 v9 ->
            coe
              MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1060))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.E
d_E_5790 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_E_5790 ~v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_E_5790 v1 v2 v3 v4 v16
du_E_5790 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_E_5790 v0 v1 v2 v3 v4
  = coe
      du_E_5320 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.build
d_build_5792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_build_5792 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 v18 v19 ~v20 ~v21 ~v22
  = du_build_5792 v2 v3 v4 v9 v17 v18 v19
du_build_5792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_build_5792 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_build_5330 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v2) (coe v3) erased
      (coe v4) (coe v5) (coe v6) erased v10
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.fs₁
d_fs'8321'_5794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5794 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
                ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20
  = du_fs'8321'_5794 v0 v1 v2 v7 v15 v16 v17
du_fs'8321'_5794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5794 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 (coe v1)
         (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v4)
         (coe v5) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.E≡
d_E'8801'_5796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E'8801'_5796 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ev-eq
d_ev'45'eq_5798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ev'45'eq_5798 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.halts-obs
d_halts'45'obs_5810 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_halts'45'obs_5810 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                    ~v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 ~v20 ~v21 ~v22
  = du_halts'45'obs_5810 v2 v3 v4 v9 v17 v18 v19
du_halts'45'obs_5810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_halts'45'obs_5810 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_build_5330 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v2) (coe v3) erased
      (coe v4) (coe v5) (coe v6) erased erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.E
d_E_5848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_E_5848 ~v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_E_5848 v1 v2 v3 v4 v16
du_E_5848 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_E_5848 v0 v1 v2 v3 v4
  = coe
      du_E_5320 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.build
d_build_5850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_build_5850 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 v18 v19 ~v20 ~v21 ~v22
  = du_build_5850 v2 v3 v4 v9 v17 v18 v19
du_build_5850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_build_5850 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_build_5330 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v2) (coe v3) erased
      (coe v4) (coe v5) (coe v6) erased v10
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.fs₁
d_fs'8321'_5852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5852 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
                ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20
  = du_fs'8321'_5852 v0 v1 v2 v7 v15 v16 v17
du_fs'8321'_5852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5852 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 (coe v1)
         (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v4)
         (coe v5) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.E≡
d_E'8801'_5854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E'8801'_5854 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ev-eq
d_ev'45'eq_5856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ev'45'eq_5856 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.fits-not-unit
d_fits'45'not'45'unit_5866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fits'45'not'45'unit_5866 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.calls-obs
d_calls'45'obs_5874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_calls'45'obs_5874 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 v21 v22 ~v23 ~v24 ~v25
  = du_calls'45'obs_5874 v2 v3 v4 v5 v8 v12 v20 v21 v22
du_calls'45'obs_5874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_calls'45'obs_5874 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_build_5330 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) erased
      (coe v6) (coe v7) (coe v8) erased
      (\ v10 v11 -> coe du_place_5974 (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.E
d_E_5918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_E_5918 ~v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_E_5918 v1 v2 v3 v4 v5 v19
du_E_5918 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_E_5918 v0 v1 v2 v3 v4 v5
  = coe
      du_E_5320 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.build
d_build_5920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_build_5920 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
             ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 v21 v22 ~v23 ~v24 ~v25
  = du_build_5920 v2 v3 v4 v5 v12 v20 v21 v22
du_build_5920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_build_5920 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_build_5330 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) erased
      (coe v5) (coe v6) (coe v7) erased v11
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.S.fs₁
d_fs'8321'_5922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5922 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
                ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19 v20 ~v21 ~v22 ~v23
  = du_fs'8321'_5922 v0 v1 v2 v3 v10 v18 v19 v20
du_fs'8321'_5922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5922 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 (coe v1)
         (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v5)
         (coe v6) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v7)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.E≡
d_E'8801'_5924 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E'8801'_5924 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.op
d_op_5926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_CallOp_124
d_op_5926 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_op_5926 v3 v4 v5
du_op_5926 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_CallOp_124
du_op_5926 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.C_callOp_142
      (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v2)) (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v2)) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.y
d_y_5928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_y_5928 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_y_5928 v2 v3 v4 v5
du_y_5928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_y_5928 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Contract.du_yes'45'of_184
      (coe
         MAlonzo.Code.Once.Spec.Contract.C_key_138
         (coe
            MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
            (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v3)))
         (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.Spec.Contract.d_answerKeys_300
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.d_sig_464
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.p₀
d_p'8320'_5930 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_p'8320'_5930 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_p'8320'_5930 v2 v3 v4 v5
du_p'8320'_5930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_p'8320'_5930 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_y_5928 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ans
d_ans_5932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  AgdaAny
d_ans_5932 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15 ~v16 ~v17 ~v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_ans_5932 v2 v3 v4 v5 v19 v20
du_ans_5932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> AgdaAny
du_ans_5932 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.d_answer_482
      (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v5))
      (coe du_op_5926 (coe v1) (coe v2) (coe v3))
      (coe du_p'8320'_5930 (coe v0) (coe v1) (coe v2) (coe v3))
      (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_356
         (coe v1) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v3))
         (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.run-call
d_run'45'call_5934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'call_5934 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._._.ans-eq
d_ans'45'eq_5940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ans'45'eq_5940 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._._._.go
d_go_5948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_5948 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.res-call
d_res'45'call_5956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_res'45'call_5956 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.ev-eq
d_ev'45'eq_5958 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ev'45'eq_5958 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.out≡
d_out'8801'_5962 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'8801'_5962 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.out-fit
d_out'45'fit_5970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'fit_5970 = erased
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC._.place
d_place_5974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_5974 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
             ~v26 ~v27
  = du_place_5974 v8
du_place_5974 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
du_place_5974 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1092
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Prelude.du_fits'45'erase_16
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.obs-correct-sigop-rest
d_obs'45'correct'45'sigop'45'rest_5990
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.obs-correct-sigop-rest"
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.pure-route
d_pure'45'route_6000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_pure'45'route_6000 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
  = du_pure'45'route_6000 v0 v1 v2 v3 v4 v5 v10
du_pure'45'route_6000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_pure'45'route_6000 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             (\ v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
                v24 ->
                coe
                  du_pure'45'obs_5658 (coe v2) (coe v3) (coe v4) (coe v5) (coe v7)
                  v11 v19 v20 v21)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_obs'45'correct'45'sigop'45'rest_5990 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.calls-route
d_calls'45'route_6032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_calls'45'route_6032 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8
  = du_calls'45'route_6032 v0 v1 v2 v3 v4 v5 v8
du_calls'45'route_6032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_calls'45'route_6032 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             (\ v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
                v24 ->
                coe
                  du_calls'45'obs_5874 (coe v2) (coe v3) (coe v4) (coe v5) (coe v7)
                  v11 v19 v20 v21)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_obs'45'correct'45'sigop'45'rest_5990 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.by-sem
d_by'45'sem_6056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_by'45'sem_6056 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_by'45'sem_6056 v0 v1 v2 v3 v4 v5 v6
du_by'45'sem_6056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_by'45'sem_6056 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_pureV_148 v7
        -> coe
             du_pure'45'route_6000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v4))
      MAlonzo.Code.Once.SigOp.Info.C_ffiV_150
        -> coe
             du_pure'45'route_6000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v4))
      MAlonzo.Code.Once.SigOp.Info.C_callsV_152
        -> coe
             du_calls'45'route_6032 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v4))
      MAlonzo.Code.Once.SigOp.Info.C_emitsV_154
        -> coe
             (\ v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
                v24 ->
                coe
                  du_emits'45'obs_5752 (coe v2) (coe v3) (coe v5) v11 v19 v20 v21)
      MAlonzo.Code.Once.SigOp.Info.C_haltsV_156
        -> coe
             (\ v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
                v24 ->
                coe
                  du_halts'45'obs_5810 (coe v2) (coe v3) (coe v5) v11 v19 v20 v21)
      MAlonzo.Code.Once.SigOp.Info.C_primV_158 v7
        -> coe
             du_pure'45'route_6000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.SigOp.SigOpC.obs-correct-sigop
d_obs'45'correct'45'sigop_6118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
d_obs'45'correct'45'sigop_6118 v0 v1 v2 v3 v4 v5 ~v6
  = du_obs'45'correct'45'sigop_6118 v0 v1 v2 v3 v4 v5
du_obs'45'correct'45'sigop_6118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_4078 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3830 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3784
du_obs'45'correct'45'sigop_6118 v0 v1 v2 v3 v4 v5
  = coe
      du_by'45'sem_6056 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v5))
