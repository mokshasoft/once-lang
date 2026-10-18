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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Prelude
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotBudget
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.CCC.Machine.ValidAtWFHalted
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.IRObsCorrect.Machine._.Σ
d_Σ_11 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InitLast
d_InitLast_13 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Bool
d_Bool_15 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.budget-of
d_budget'45'of_16 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_16 ~v0 ~v1 = du_budget'45'of_16
du_budget'45'of_16 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_budget'45'of_16
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_budget'45'of_74
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⊤
d_'8868'_17 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.fits-erase
d_fits'45'erase_18 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
d_fits'45'erase_18 ~v0 ~v1 = du_fits'45'erase_18
du_fits'45'erase_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
du_fits'45'erase_18 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Prelude.du_fits'45'erase_16
      v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.frontier-mono
d_frontier'45'mono_20 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_20 v0 ~v1 = du_frontier'45'mono_20 v0
du_frontier'45'mono_20 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_frontier'45'mono_20 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotBudget.d_frontier'45'mono_156
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ir-to-trace
d_ir'45'to'45'trace_22 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_ir'45'to'45'trace_22 v0 ~v1 = du_ir'45'to'45'trace_22 v0
du_ir'45'to'45'trace_22 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_ir'45'to'45'trace_22 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_860
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ir-to-trace'
d_ir'45'to'45'trace''_24 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_24 v0 ~v1 = du_ir'45'to'45'trace''_24 v0
du_ir'45'to'45'trace''_24 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ir'45'to'45'trace''_24 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.validAtWF-set-halted
d_validAtWF'45'set'45'halted_26 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validAtWF'45'set'45'halted_26 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ValidAtWFHalted.du_validAtWF'45'set'45'halted_1256
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.AllI→All
d_AllI'8594'All_30 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_AllI'8594'All_30 ~v0 ~v1 = du_AllI'8594'All_30
du_AllI'8594'All_30 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_AllI'8594'All_30 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_AllI'8594'All_158
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.All→AllI
d_All'8594'AllI_32 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_All'8594'AllI_32 ~v0 ~v1 = du_All'8594'AllI_32
du_All'8594'AllI_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_All'8594'AllI_32 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_All'8594'AllI_104
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.BlockStable
d_BlockStable_34 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockStable_34 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.all-stable?
d_all'45'stable'63'_36 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> Bool
d_all'45'stable'63'_36 v0 ~v1 = du_all'45'stable'63'_36 v0
du_all'45'stable'63'_36 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> Bool
du_all'45'stable'63'_36 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_all'45'stable'63'_112
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.all-stable?-++
d_all'45'stable'63''45''43''43'_38 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45''43''43'_38 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.all-stable?-complete
d_all'45'stable'63''45'complete_40 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45'complete_40 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.all-stable?-sound
d_all'45'stable'63''45'sound_42 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'stable'63''45'sound_42 v0 ~v1
  = du_all'45'stable'63''45'sound_42 v0
du_all'45'stable'63''45'sound_42 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'stable'63''45'sound_42 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_all'45'stable'63''45'sound_134
      (coe v0) v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.bds
d_bds_44 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bds_44 ~v0 ~v1 = du_bds_44
du_bds_44 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_bds_44 v0 v1
  = coe MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_bds_662 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.blocks-stable
d_blocks'45'stable_46 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'stable_46 ~v0 ~v1 = du_blocks'45'stable_46
du_blocks'45'stable_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'stable_46 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_blocks'45'stable_672
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-body-stable
d_cata'45'body'45'stable_48 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'body'45'stable_48 ~v0 ~v1 = du_cata'45'body'45'stable_48
du_cata'45'body'45'stable_48 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'body'45'stable_48 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'body'45'stable_352
      v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-dispatch-slot-stable
d_cata'45'dispatch'45'slot'45'stable_50 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'dispatch'45'slot'45'stable_50 v0 ~v1
  = du_cata'45'dispatch'45'slot'45'stable_50 v0
du_cata'45'dispatch'45'slot'45'stable_50 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'dispatch'45'slot'45'stable_50 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'dispatch'45'slot'45'stable_468
      (coe v0) v1 v2 v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-trace-branching-stable
d_cata'45'trace'45'branching'45'stable_52 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'branching'45'stable_52 v0 ~v1
  = du_cata'45'trace'45'branching'45'stable_52 v0
du_cata'45'trace'45'branching'45'stable_52 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'branching'45'stable_52 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'branching'45'stable_434
      (coe v0) v1 v2 v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-trace-const-stable
d_cata'45'trace'45'const'45'stable_54 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'const'45'stable_54 v0 ~v1
  = du_cata'45'trace'45'const'45'stable_54 v0
du_cata'45'trace'45'const'45'stable_54 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'const'45'stable_54 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'const'45'stable_372
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-trace-linear-stable
d_cata'45'trace'45'linear'45'stable_56 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'linear'45'stable_56 v0 ~v1
  = du_cata'45'trace'45'linear'45'stable_56 v0
du_cata'45'trace'45'linear'45'stable_56 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'linear'45'stable_56 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'linear'45'stable_412
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-trace-nat-stable
d_cata'45'trace'45'nat'45'stable_58 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'nat'45'stable_58 v0 ~v1
  = du_cata'45'trace'45'nat'45'stable_58 v0
du_cata'45'trace'45'nat'45'stable_58 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'nat'45'stable_58 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'nat'45'stable_392
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.ir-blocks-stable
d_ir'45'blocks'45'stable_60 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'blocks'45'stable_60 v0 ~v1
  = du_ir'45'blocks'45'stable_60 v0
du_ir'45'blocks'45'stable_60 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'blocks'45'stable_60 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'blocks'45'stable_776
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.ir-stable
d_ir'45'stable_62 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_62 v0 ~v1 = du_ir'45'stable_62 v0
du_ir'45'stable_62 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'stable_62 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'stable_550
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.ir-to-trace-lab-slot-stable
d_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 v0 ~v1
  = du_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 v0
du_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'lab'45'slot'45'stable_906
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_66 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_66 v0 ~v1
  = du_ir'45'to'45'trace'45'slot'45'stable_66 v0
du_ir'45'to'45'trace'45'slot'45'stable_66 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'slot'45'stable_66 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_894
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.ir-to-trace-top-slot-stable
d_ir'45'to'45'trace'45'top'45'slot'45'stable_68 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'top'45'slot'45'stable_68 v0 ~v1
  = du_ir'45'to'45'trace'45'top'45'slot'45'stable_68 v0
du_ir'45'to'45'trace'45'top'45'slot'45'stable_68 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'top'45'slot'45'stable_68 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'top'45'slot'45'stable_918
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.rebuild-walk-stable
d_rebuild'45'walk'45'stable_70 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'walk'45'stable_70 v0 ~v1
  = du_rebuild'45'walk'45'stable_70 v0
du_rebuild'45'walk'45'stable_70 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'walk'45'stable_70 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_rebuild'45'walk'45'stable_294
      (coe v0) v1 v2 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.resuspend-stable
d_resuspend'45'stable_72 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_resuspend'45'stable_72 v0 ~v1 = du_resuspend'45'stable_72 v0
du_resuspend'45'stable_72 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_resuspend'45'stable_72 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_resuspend'45'stable_698
      (coe v0) v2 v3 v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.sigop-stable
d_sigop'45'stable_74 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sigop'45'stable_74 v0 ~v1 = du_sigop'45'stable_74 v0
du_sigop'45'stable_74 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_sigop'45'stable_74 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_sigop'45'stable_524
      (coe v0) v1 v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.stable?
d_stable'63'_76 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> Bool
d_stable'63'_76 v0 ~v1 = du_stable'63'_76 v0
du_stable'63'_76 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> Bool
du_stable'63'_76 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_stable'63'_110
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.stable?-complete
d_stable'63''45'complete_78 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable'63''45'complete_78 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.stable?-sound
d_stable'63''45'sound_80 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_stable'63''45'sound_80 v0 ~v1 = du_stable'63''45'sound_80 v0
du_stable'63''45'sound_80 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_stable'63''45'sound_80 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_stable'63''45'sound_130
      (coe v0) v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.trc
d_trc_82 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_trc_82 ~v0 ~v1 = du_trc_82
du_trc_82 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_trc_82 v0 v1
  = coe MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_trc_98 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.visit-walk-stable
d_visit'45'walk'45'stable_84 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_visit'45'walk'45'stable_84 v0 ~v1
  = du_visit'45'walk'45'stable_84 v0
du_visit'45'walk'45'stable_84 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_visit'45'walk'45'stable_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_visit'45'walk'45'stable_232
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.∧-intro
d_'8743''45'intro_86 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'intro_86 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.∧-split
d_'8743''45'split_88 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_88 ~v0 ~v1 = du_'8743''45'split_88
du_'8743''45'split_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_88 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_'8743''45'split_126
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.BodyCorrect
d_BodyCorrect_94 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.CellAt
d_CellAt_98 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF
d_ClosureValidWF_100 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed
d_ClosureWellFormed_104 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                        a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.EnvAt
d_EnvAt_108 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget
d_IRHeapBudget_110 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF
d_IRResultAWF_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase
d_IRResultBase_118 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget
d_IRStackBudget_122 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF
d_InlValidWF_128 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlineRep
d_InlineRep_132 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InputPlace
d_InputPlace_134 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF
d_InrValidWF_136 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PairValidWF
d_PairValidWF_140 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PayloadAt
d_PayloadAt_144 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.Place
d_Place_146 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.RecDispatcherWF
d_RecDispatcherWF_148 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> ()
d_RecDispatcherWF_148 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ResultPlace
d_ResultPlace_150 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.SumTag
d_SumTag_152 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_152 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_154 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.alloc-correct
d_alloc'45'correct_156 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_156 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.base
d_base_162 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658
d_base_162 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.before-frontier-monotone
d_before'45'frontier'45'monotone_164 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_before'45'frontier'45'monotone_164 ~v0 ~v1
  = du_before'45'frontier'45'monotone_164
du_before'45'frontier'45'monotone_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
du_before'45'frontier'45'monotone_164 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_before'45'frontier'45'monotone_5914
      v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.body-cap-eq
d_body'45'cap'45'eq_166 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_766 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_166 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.body-capacity
d_body'45'capacity_168 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_766 ->
  Integer
d_body'45'capacity_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'capacity_1464
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.body-correct
d_body'45'correct_170 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_766
d_body'45'correct_170 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'correct_1602
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.bump
d_bump_172 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850
d_bump_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1138
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_174 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1266
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_176 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_176 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1214
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.code-before
d_code'45'before_182 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_code'45'before_182 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_code'45'before_1594
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.code-ptr
d_code'45'ptr_184 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_184 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.decomposeClosureWF
d_decomposeClosureWF_186 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650
d_decomposeClosureWF_186 ~v0 ~v1 = du_decomposeClosureWF_186
du_decomposeClosureWF_186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650
du_decomposeClosureWF_186 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1720
      v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.decomposeInlWF
d_decomposeInlWF_188 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2006
d_decomposeInlWF_188 ~v0 ~v1 = du_decomposeInlWF_188
du_decomposeInlWF_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2006
du_decomposeInlWF_188 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeInlWF_2096
      v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.decomposeInrWF
d_decomposeInrWF_190 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2050
d_decomposeInrWF_190 ~v0 ~v1 = du_decomposeInrWF_190
du_decomposeInrWF_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2050
du_decomposeInrWF_190 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeInrWF_2138
      v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.decomposePairWF
d_decomposePairWF_192 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874
d_decomposePairWF_192 ~v0 ~v1 = du_decomposePairWF_192
du_decomposePairWF_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874
du_decomposePairWF_192 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1916
      v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.derive-mem-preserved
d_derive'45'mem'45'preserved_194 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved_194 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.derive-mem-preserved-at
d_derive'45'mem'45'preserved'45'at_196 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved'45'at_196 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.env-before
d_env'45'before_200 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_env'45'before_200 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'before_1592
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.env-ptr
d_env'45'ptr_204 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_204 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.env-valid
d_env'45'valid_206 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_env'45'valid_206 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'valid_1600
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.evalᴰ
d_eval'7472'_208 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_eval'7472'_208 ~v0 v1 = du_eval'7472'_208 v1
du_eval'7472'_208 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
du_eval'7472'_208 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval'7472'_24
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.execute
d_execute_210 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_766 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_210 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_execute_1482
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.final-alloc
d_final'45'alloc_212 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_final'45'alloc_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_212 v9 v10
du_final'45'alloc_212 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_final'45'alloc_212 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1168
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.final-state
d_final'45'state_214 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_final'45'state_214 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1134
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.frame-preserved
d_frame'45'preserved_216 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_216 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.frontier-slot-stable
d_frontier'45'slot'45'stable_218 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_218 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1224
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.heap-budget
d_heap'45'budget_220 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_heap'45'budget_220 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1262
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.heap-inv
d_heap'45'inv_222 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676
d_heap'45'inv_222 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.heap-monotone
d_heap'45'monotone_224 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_224 v9
du_heap'45'monotone_224 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_224 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1272
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.heap-preserved-of
d_heap'45'preserved'45'of_226 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'preserved'45'of_226 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.inline-sv
d_inline'45'sv_234 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_234 ~v0 ~v1 = du_inline'45'sv_234
du_inline'45'sv_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_234 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_566
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.input-read
d_input'45'read_236 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1780 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'read_236 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.input-sv
d_input'45'sv_238 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1780 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_input'45'sv_238 ~v0 ~v1 = du_input'45'sv_238
du_input'45'sv_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1780 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_input'45'sv_238 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_input'45'sv_1812
      v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.inputPlace-transport
d_inputPlace'45'transport_240 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1780 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1780
d_inputPlace'45'transport_240 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inputPlace'45'transport_5560
      (coe v0) (coe v1) v2 v3 v5 v6 v7 v8 v9 v10 v12 v13
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ir-returns
d_ir'45'returns_242 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_ir'45'returns_242 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ir'45'returns_1148
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.irresult-mem-preserved
d_irresult'45'mem'45'preserved_244 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irresult'45'mem'45'preserved_244 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mEnv
d_mEnv_246 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_246 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_mEnv_1598
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_248 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_248 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1268
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-heap-ref-written
d_max'45'heap'45'ref'45'written_250 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_max'45'heap'45'ref'45'written_250 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1264
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_252 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_252 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1270
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-slot-geq-final
d_max'45'slot'45'geq'45'final_254 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_254 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1216
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_256 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_256 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1218
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-slot-written
d_max'45'slot'45'written_258 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_max'45'slot'45'written_258 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1210
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mem-preserved-before
d_mem'45'preserved'45'before_260 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_260 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mem-preserved-compose
d_mem'45'preserved'45'compose_262 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'compose_262 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mem-preserved-from-tnhw
d_mem'45'preserved'45'from'45'tnhw_264 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'from'45'tnhw_264 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mk-IRResultAWF-via-bump
d_mk'45'IRResultAWF'45'via'45'bump_266 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692
d_mk'45'IRResultAWF'45'via'45'bump_266 ~v0 ~v1
  = du_mk'45'IRResultAWF'45'via'45'bump_266
du_mk'45'IRResultAWF'45'via'45'bump_266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692
du_mk'45'IRResultAWF'45'via'45'bump_266 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
                                        v24 v25
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_mk'45'IRResultAWF'45'via'45'bump_750
      v8 v10 v11 v16 v17 v18 v21 v23 v24 v25
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.not-halted
d_not'45'halted_268 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_268 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.obs-budget
d_obs'45'budget_270 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_obs'45'budget_270 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1146
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.payload-read
d_payload'45'read_276 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1936 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'read_276 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.payload-sv
d_payload'45'sv_278 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1936 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_payload'45'sv_278 ~v0 ~v1 = du_payload'45'sv_278
du_payload'45'sv_278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1936 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_payload'45'sv_278 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_payload'45'sv_1968
      v3 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.place-rax
d_place'45'rax_280 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_place'45'rax_280 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.place-sv
d_place'45'sv_282 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_place'45'sv_282 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_place'45'sv_626
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.prim-sv
d_prim'45'sv_284 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_284 ~v0 ~v1 = du_prim'45'sv_284
du_prim'45'sv_284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_284 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_548
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.reclaim-alloc
d_reclaim'45'alloc_286 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_reclaim'45'alloc_286 ~v0 ~v1 = du_reclaim'45'alloc_286
du_reclaim'45'alloc_286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_reclaim'45'alloc_286 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_reclaim'45'alloc_5594
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.reclaim-preserves-frontier
d_reclaim'45'preserves'45'frontier_288 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_reclaim'45'preserves'45'frontier_288 ~v0 ~v1
  = du_reclaim'45'preserves'45'frontier_288
du_reclaim'45'preserves'45'frontier_288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
du_reclaim'45'preserves'45'frontier_288 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_reclaim'45'preserves'45'frontier_5608
      v3 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.result-place
d_result'45'place_294 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_result'45'place_294 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1150
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.scratch-bounded
d_scratch'45'bounded_296 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_296 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1236
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.scratch-budget
d_scratch'45'budget_298 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_scratch'45'budget_298 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1234
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.slot-monotone
d_slot'45'monotone_300 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_300 v9
du_slot'45'monotone_300 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_300 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1238
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_302 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_302 v9 v10
du_slot'45'stays'45'in'45'budget_302 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_302 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1240
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1138
         (coe
            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.stack-budget
d_stack'45'budget_304 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_stack'45'budget_304 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1212
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.stack-inv
d_stack'45'inv_306 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668
d_stack'45'inv_306 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.sucLoc-before
d_sucLoc'45'before_308 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_sucLoc'45'before_308 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1596
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace
d_trace_310 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_trace_310 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1136
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-correct
d_trace'45'correct_312 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_312 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_314 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_314 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_316 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_316 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1166
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-preserves-halted
d_trace'45'preserves'45'halted_318 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_318 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_320 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_320 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1228
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_322 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_322 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1232
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-twf
d_trace'45'twf_324 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944
d_trace'45'twf_324 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1158
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-writes-above
d_trace'45'writes'45'above_326 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'writes'45'above_326 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1226
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-writes-below
d_trace'45'writes'45'below_328 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'writes'45'below_328 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1230
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.transport-SumTag
d_transport'45'SumTag_330 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_transport'45'SumTag_330 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.valid-primitive-wf
d_valid'45'primitive'45'wf_352 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_valid'45'primitive'45'wf_352 ~v0 ~v1
  = du_valid'45'primitive'45'wf_352
du_valid'45'primitive'45'wf_352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
du_valid'45'primitive'45'wf_352 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'primitive'45'wf_598
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.valid-to-validWF-unit
d_valid'45'to'45'validWF'45'unit_354 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_valid'45'to'45'validWF'45'unit_354 ~v0 ~v1
  = du_valid'45'to'45'validWF'45'unit_354
du_valid'45'to'45'validWF'45'unit_354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
du_valid'45'to'45'validWF'45'unit_354 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'to'45'validWF'45'unit_2174
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-alloc-advance
d_validityWF'45'alloc'45'advance_362 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'alloc'45'advance_362 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'alloc'45'advance_4068
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_364 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'frontier'45'advance_364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4408
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v11 v12 v13
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-mem-only
d_validityWF'45'mem'45'only_366 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'mem'45'only_366 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'only_2190
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_368 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'mem'45'preserved_368 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5160
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-reclaim
d_validityWF'45'reclaim_370 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'reclaim_370 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'reclaim_5692
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v10 v12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-trace-preserves
d_validityWF'45'trace'45'preserves_372 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'trace'45'preserves_372 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'trace'45'preserves_5832
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_374 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'with'45'bf'45'transfer_374 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'with'45'bf'45'transfer_4824
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v10 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-write-at-frontier
d_validityWF'45'write'45'at'45'frontier_376 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'write'45'at'45'frontier_376 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'at'45'frontier_2578
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-write-at-suc-frontier
d_validityWF'45'write'45'at'45'suc'45'frontier_378 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'write'45'at'45'suc'45'frontier_378 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'at'45'suc'45'frontier_2950
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-write-sv-at-frontier
d_validityWF'45'write'45'sv'45'at'45'frontier_380 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'write'45'sv'45'at'45'frontier_380 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'sv'45'at'45'frontier_3322
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-write-sv-at-suc-frontier
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_382 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_382 v0 v1 v2
                                                         v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3694
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ιᶠ
d_ι'7584'_384 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
d_ι'7584'_384 ~v0 ~v1 = du_ι'7584'_384
du_ι'7584'_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
du_ι'7584'_384
  = coe MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_ι'7584'_26
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.BodyCorrect.body-cap-eq
d_body'45'cap'45'eq_388 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_766 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_388 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.BodyCorrect.body-capacity
d_body'45'capacity_390 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_766 ->
  Integer
d_body'45'capacity_390 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'capacity_1464
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.BodyCorrect.execute
d_execute_392 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_766 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_392 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_execute_1482
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.EnvType
d_EnvType_402 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_402 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_EnvType_1684
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.body
d_body_404 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_body_404 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body_1686
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.body-label
d_body'45'label_406 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_406 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'label_1690
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.code-ptr
d_code'45'ptr_408 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_408 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.env
d_env_410 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  AgdaAny
d_env_410 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env_1688 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.env-at
d_env'45'at_412 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616
d_env'45'at_412 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'at_1694
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_414 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_414 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.loc-mode
d_loc'45'mode_416 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  AgdaAny
d_loc'45'mode_416 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_loc'45'mode_1692
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_418 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_sucLoc'45'before_418 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1698
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.body-correct
d_body'45'correct_422 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_766
d_body'45'correct_422 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'correct_1602
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.code-before
d_code'45'before_424 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_code'45'before_424 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_code'45'before_1594
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.code-ptr
d_code'45'ptr_426 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_426 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.env-before
d_env'45'before_428 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_env'45'before_428 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'before_1592
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.env-ptr
d_env'45'ptr_430 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_430 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.env-valid
d_env'45'valid_432 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_env'45'valid_432 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'valid_1600
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.mEnv
d_mEnv_434 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_434 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_mEnv_1598
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.sucLoc-before
d_sucLoc'45'before_436 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1546 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_sucLoc'45'before_436 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1596
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_446 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_446 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1266
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.heap-budget
d_heap'45'budget_448 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676 ->
  Integer
d_heap'45'budget_448 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1262
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.heap-monotone
d_heap'45'monotone_450 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_450 ~v0 ~v1 = du_heap'45'monotone_450
du_heap'45'monotone_450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_450 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1272
      v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_452 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_452 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1268
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-written
d_max'45'heap'45'ref'45'written_454 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676 ->
  Integer
d_max'45'heap'45'ref'45'written_454 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1264
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_456 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_456 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1270
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.alloc-correct
d_alloc'45'correct_460 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_460 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.base
d_base_462 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658
d_base_462 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.bump
d_bump_464 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850
d_bump_464 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1138
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_466 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_466 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1266
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_468 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_468 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1214
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.final-alloc
d_final'45'alloc_470 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_final'45'alloc_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_470 v9 v10
du_final'45'alloc_470 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_final'45'alloc_470 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1168
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.final-state
d_final'45'state_472 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_final'45'state_472 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1134
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.frame-preserved
d_frame'45'preserved_474 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_474 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.frontier-slot-stable
d_frontier'45'slot'45'stable_476 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_476 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1224
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.heap-budget
d_heap'45'budget_478 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_heap'45'budget_478 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1262
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.heap-inv
d_heap'45'inv_480 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_676
d_heap'45'inv_480 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.heap-monotone
d_heap'45'monotone_482 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_482 v9
du_heap'45'monotone_482 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_482 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1272
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.ir-returns
d_ir'45'returns_484 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_ir'45'returns_484 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ir'45'returns_1148
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_486 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_486 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1268
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-heap-ref-written
d_max'45'heap'45'ref'45'written_488 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_max'45'heap'45'ref'45'written_488 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1264
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_490 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_490 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1270
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1300
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-slot-geq-final
d_max'45'slot'45'geq'45'final_492 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_492 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1216
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_494 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_494 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1218
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-slot-written
d_max'45'slot'45'written_496 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_max'45'slot'45'written_496 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1210
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.mem-preserved-before
d_mem'45'preserved'45'before_498 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_498 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.not-halted
d_not'45'halted_500 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_500 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.obs-budget
d_obs'45'budget_502 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_obs'45'budget_502 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1146
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.result-place
d_result'45'place_504 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_result'45'place_504 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1150
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.scratch-bounded
d_scratch'45'bounded_506 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_506 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1236
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.scratch-budget
d_scratch'45'budget_508 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_scratch'45'budget_508 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1234
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.slot-monotone
d_slot'45'monotone_510 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_510 v9
du_slot'45'monotone_510 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_510 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1238
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_512 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_512 v9 v10
du_slot'45'stays'45'in'45'budget_512 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_512 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1240
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1138
         (coe
            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.stack-budget
d_stack'45'budget_514 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  Integer
d_stack'45'budget_514 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1212
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.stack-inv
d_stack'45'inv_516 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668
d_stack'45'inv_516 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace
d_trace_518 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_trace_518 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1136
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-correct
d_trace'45'correct_520 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_520 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_522 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_522 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_524 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_524 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1166
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-preserves-halted
d_trace'45'preserves'45'halted_526 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_526 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_528 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_528 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1228
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_530 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_530 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1232
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-twf
d_trace'45'twf_532 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944
d_trace'45'twf_532 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1158
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1296
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-writes-above
d_trace'45'writes'45'above_534 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'writes'45'above_534 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1226
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-writes-below
d_trace'45'writes'45'below_536 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_692 ->
  AgdaAny
d_trace'45'writes'45'below_536 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1230
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1298
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.alloc-correct
d_alloc'45'correct_540 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_540 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.bump
d_bump_542 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850
d_bump_542 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1138
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.final-alloc
d_final'45'alloc_544 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_final'45'alloc_544 ~v0 ~v1 = du_final'45'alloc_544
du_final'45'alloc_544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_final'45'alloc_544 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1168
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.final-state
d_final'45'state_546 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_final'45'state_546 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1134
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.frame-preserved
d_frame'45'preserved_548 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_548 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.ir-returns
d_ir'45'returns_550 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  AgdaAny
d_ir'45'returns_550 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ir'45'returns_1148
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.mem-preserved-before
d_mem'45'preserved'45'before_552 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_552 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.not-halted
d_not'45'halted_554 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_554 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.obs-budget
d_obs'45'budget_556 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  Integer
d_obs'45'budget_556 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1146
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.result-place
d_result'45'place_558 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_result'45'place_558 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1150
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace
d_trace_560 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_trace_560 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1136
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-correct
d_trace'45'correct_562 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_562 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_564 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_564 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_566 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_566 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1166
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-preserves-halted
d_trace'45'preserves'45'halted_568 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_568 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-twf
d_trace'45'twf_570 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_658 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_7944
d_trace'45'twf_570 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1158
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_574 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_574 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1214
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.frontier-slot-stable
d_frontier'45'slot'45'stable_576 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_576 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1224
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.max-slot-geq-final
d_max'45'slot'45'geq'45'final_578 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_578 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1216
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_580 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_580 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1218
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.max-slot-written
d_max'45'slot'45'written_582 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  Integer
d_max'45'slot'45'written_582 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1210
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.scratch-bounded
d_scratch'45'bounded_584 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_584 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1236
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.scratch-budget
d_scratch'45'budget_586 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  Integer
d_scratch'45'budget_586 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1234
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.slot-monotone
d_slot'45'monotone_588 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_588 ~v0 ~v1 = du_slot'45'monotone_588
du_slot'45'monotone_588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_588 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1238
      v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_590 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_590 ~v0 ~v1
  = du_slot'45'stays'45'in'45'budget_590
du_slot'45'stays'45'in'45'budget_590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_850 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_590 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1240
      v1 v2 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.stack-budget
d_stack'45'budget_592 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  Integer
d_stack'45'budget_592 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1212
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_594 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_594 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1228
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_596 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_596 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1232
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.trace-writes-above
d_trace'45'writes'45'above_598 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  AgdaAny
d_trace'45'writes'45'above_598 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1226
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.trace-writes-below
d_trace'45'writes'45'below_600 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_668 ->
  AgdaAny
d_trace'45'writes'45'below_600 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1230
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF.a
d_a_604 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2006 ->
  AgdaAny
d_a_604 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_a_2028 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF.payload
d_payload_606 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2006 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1936
d_payload_606 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_payload_2032
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF.sucLoc-before
d_sucLoc'45'before_608 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2006 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_sucLoc'45'before_608 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_2030
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF.v-is-inl
d_v'45'is'45'inl_610 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2006 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_610 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF.b
d_b_628 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2050 ->
  AgdaAny
d_b_628 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_b_2072 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF.payload
d_payload_630 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2050 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1936
d_payload_630 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_payload_2076
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF.sucLoc-before
d_sucLoc'45'before_632 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2050 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_sucLoc'45'before_632 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_2074
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF.v-is-inr
d_v'45'is'45'inr_634 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_634 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PairValidWF.fst-cell
d_fst'45'cell_638 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578
d_fst'45'cell_638 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1896
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PairValidWF.snd-cell
d_snd'45'cell_640 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578
d_snd'45'cell_640 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1898
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PairValidWF.sucLoc-before
d_sucLoc'45'before_642 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_sucLoc'45'before_642 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1894
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.AllSlotStable
d_AllSlotStable_694 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_AllSlotStable_694 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BeforeFrontier
d_BeforeFrontier_696 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlockAt
d_BlockAt_698 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockAt_698 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlockRuns
d_BlockRuns_700 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlocksAt
d_BlocksAt_704 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_BlocksAt_704 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CallPost
d_CallPost_706 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun
d_CalleeRun_708 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRuns
d_CalleeRuns_712 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_CalleeRuns_712 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CellAt
d_CellAt_714 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CoalgRuns
d_CoalgRuns_716 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_CoalgRuns_716 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.EnvAt
d_EnvAt_718 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState
d_FlatState_720 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatSteps
d_FlatSteps_724 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatSteps-++
d_FlatSteps'45''43''43'_726 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_FlatSteps'45''43''43'_726 ~v0 ~v1 ~v2
  = du_FlatSteps'45''43''43'_726
du_FlatSteps'45''43''43'_726 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_FlatSteps'45''43''43'_726 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1170
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatSteps-prefix
d_FlatSteps'45'prefix_728 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_FlatSteps'45'prefix_728 ~v0 ~v1 ~v2 = du_FlatSteps'45'prefix_728
du_FlatSteps'45'prefix_728 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_FlatSteps'45'prefix_728 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'prefix_998
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatSteps-reloc
d_FlatSteps'45'reloc_730 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_FlatSteps'45'reloc_730 ~v0 ~v1 ~v2 = du_FlatSteps'45'reloc_730
du_FlatSteps'45'reloc_730 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_FlatSteps'45'reloc_730 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'reloc_1040
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlinkView
d_FlinkView_732 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FnRuns
d_FnRuns_734 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_FnRuns_734 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.IRObsCorrectF
d_IRObsCorrectF_736 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_736 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.InlineRep
d_InlineRep_738 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.InputAt
d_InputAt_740 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.InstrWF
d_InstrWF_742 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> ()
d_InstrWF_742 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.LabelsAt
d_LabelsAt_744 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_LabelsAt_744 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.MachineRefinesObsF
d_MachineRefinesObsF_746 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ProgFree
d_ProgFree_750 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> ()
d_ProgFree_750 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.Readable
d_Readable_752 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ResultPlace
d_ResultPlace_754 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.Shifted
d_Shifted_756 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Shifted_756 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.SpanAt
d_SpanAt_758 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_SpanAt_758 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.Straight
d_Straight_760 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_Straight_760 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.StraightStep
d_StraightStep_762 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> ()
d_StraightStep_762 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValidAtWF
d_ValidAtWF_764 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized
d_ValueRealized_766 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.blocks
d_blocks_776 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_776 v0 ~v1 = du_blocks_776 v0
du_blocks_776 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_blocks_776 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_1978
      (coe v0) v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.callView
d_callView_778 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350
d_callView_778 ~v0 ~v1 v2 = du_callView_778 v2
du_callView_778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350
du_callView_778 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1368 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.cata-correct
d_cata'45'correct_782 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286) ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286
d_cata'45'correct_782 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cata'45'correct_2642
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.chain-events
d_chain'45'events_788 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_chain'45'events_788 ~v0 ~v1 v2 = du_chain'45'events_788 v2
du_chain'45'events_788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_chain'45'events_788 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_650
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.chain-events-++
d_chain'45'events'45''43''43'_790 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_790 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.chain-events-nil
d_chain'45'events'45'nil_792 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_792 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.chain-events-subst-start
d_chain'45'events'45'subst'45'start_794 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_794 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.chain-left
d_chain'45'left_796 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'left_796 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.decomposeClosureWF
d_decomposeClosureWF_802 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650
d_decomposeClosureWF_802 ~v0 ~v1 ~v2 = du_decomposeClosureWF_802
du_decomposeClosureWF_802 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650
du_decomposeClosureWF_802 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1720
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.decomposePairWF
d_decomposePairWF_804 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874
d_decomposePairWF_804 ~v0 ~v1 ~v2 = du_decomposePairWF_804
du_decomposePairWF_804 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874
du_decomposePairWF_804 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1916
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-branch
d_do'45'branch_806 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_806 ~v0 ~v1 v2 = du_do'45'branch_806 v2
du_do'45'branch_806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch_806 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_938 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-branch-at
d_do'45'branch'45'at_808 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch'45'at_808 ~v0 ~v1 ~v2 = du_do'45'branch'45'at_808
du_do'45'branch'45'at_808 ::
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch'45'at_808
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'branch'45'at_930
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call
d_do'45'call_810 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_810 ~v0 ~v1 v2 = du_do'45'call_810 v2
du_do'45'call_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call_810 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-at
d_do'45'call'45'at_812 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_812 ~v0 ~v1 v2 = du_do'45'call'45'at_812 v2
du_do'45'call'45'at_812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'at_812 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1284 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-code
d_do'45'call'45'code_814 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'code_814 ~v0 ~v1 v2 = du_do'45'call'45'code_814 v2
du_do'45'call'45'code_814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'code_814 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'code_1292
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-code-prefix
d_do'45'call'45'code'45'prefix_816 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'code'45'prefix_816 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-prefix
d_do'45'call'45'prefix_818 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'prefix_818 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-sv
d_do'45'call'45'sv_820 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'sv_820 ~v0 ~v1 v2 = du_do'45'call'45'sv_820 v2
du_do'45'call'45'sv_820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'sv_820 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'sv_1316 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-sv-prefix
d_do'45'call'45'sv'45'prefix_822 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'sv'45'prefix_822 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-jump
d_do'45'jump_824 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_824 ~v0 ~v1 ~v2 = du_do'45'jump_824
du_do'45'jump_824 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_824
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_922
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret
d_do'45'ret_826 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_826 ~v0 ~v1 ~v2 = du_do'45'ret_826
du_do'45'ret_826 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_826
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_1140
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-alloc
d_do'45'ret'45'alloc_828 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_828 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_830 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_830 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_832 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_832 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_834 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_834 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_836 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_836 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-save-closure
d_do'45'save'45'closure_838 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'save'45'closure_838 ~v0 ~v1 ~v2
  = du_do'45'save'45'closure_838
du_do'45'save'45'closure_838 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'save'45'closure_838
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1498
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-thunk
d_do'45'thunk_840 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_840 ~v0 ~v1 v2 = du_do'45'thunk_840 v2
du_do'45'thunk_840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_840 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1274 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.emitted
d_emitted_842 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_emitted_842 v0 ~v1 = du_emitted_842 v0
du_emitted_842 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_emitted_842 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_1966
      (coe v0) v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.enter-call
d_enter'45'call_844 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_enter'45'call_844 ~v0 ~v1 v2 = du_enter'45'call_844 v2
du_enter'45'call_844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'call_844 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.enter-frame
d_enter'45'frame_846 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_enter'45'frame_846 ~v0 ~v1 v2 = du_enter'45'frame_846 v2
du_enter'45'frame_846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'frame_846 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'frame_954 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.entry-flat
d_entry'45'flat_848 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_entry'45'flat_848 ~v0 ~v1 = du_entry'45'flat_848
du_entry'45'flat_848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_entry'45'flat_848 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_entry'45'flat_1986
      v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.entry-of?
d_entry'45'of'63'_850 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
d_entry'45'of'63'_850 ~v0 ~v1 ~v2 = du_entry'45'of'63'_850
du_entry'45'of'63'_850 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
du_entry'45'of'63'_850
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63'_168
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.entry-of?-sound
d_entry'45'of'63''45'sound_852 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'of'63''45'sound_852 ~v0 ~v1 ~v2
  = du_entry'45'of'63''45'sound_852
du_entry'45'of'63''45'sound_852 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'of'63''45'sound_852 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63''45'sound_634
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.entry→thunk
d_entry'8594'thunk_854 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8594'thunk_854 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.evalᴰ
d_eval'7472'_860 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_eval'7472'_860 ~v0 v1 = du_eval'7472'_860 v1
du_eval'7472'_860 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
du_eval'7472'_860 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_1156
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.event-of
d_event'45'of_862 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_event'45'of_862 ~v0 ~v1 ~v2 = du_event'45'of_862
du_event'45'of_862 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_event'45'of_862
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_504
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.eventsAt
d_eventsAt_864 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_eventsAt_864 ~v0 ~v1 = du_eventsAt_864
du_eventsAt_864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_eventsAt_864 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eventsAt_1168
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract
d_exec'45'abstract_866 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_866 ~v0 ~v1 v2 = du_exec'45'abstract_866 v2
du_exec'45'abstract_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_866 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3210
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-load-indirect-output
d_exec'45'abstract'45'load'45'indirect'45'output_868 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'output_868 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-load-indirect-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_870 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_870
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-load-indirect-suc-output
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_872 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_872
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-load-indirect-suc-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_874 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_874
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_876 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_876 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-halted-WF
d_exec'45'abstract'45'preserves'45'halted'45'WF_878 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted'45'WF_878 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-heap-ref
d_exec'45'abstract'45'preserves'45'heap'45'ref_880 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heap'45'ref_880 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_882 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_882 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_884 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_884 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat
d_exec'45'flat_886 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_886 ~v0 ~v1 v2 = du_exec'45'flat_886 v2
du_exec'45'flat_886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_exec'45'flat_886 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3688 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-halted
d_exec'45'flat'45'halted_888 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_888 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-invariant
d_exec'45'flat'45'invariant_890 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_890 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-keeps-next-slot
d_exec'45'flat'45'keeps'45'next'45'slot_892 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'keeps'45'next'45'slot_892 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-offend
d_exec'45'flat'45'offend_894 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_894 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-reloc
d_exec'45'flat'45'reloc_896 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'flat'45'reloc_896 ~v0 ~v1 v2
  = du_exec'45'flat'45'reloc_896 v2
du_exec'45'flat'45'reloc_896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'flat'45'reloc_896 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'flat'45'reloc_3738
      (coe v0) v1 v2 v3 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-step
d_exec'45'flat'45'step_898 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_898 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-steps
d_exec'45'flat'45'steps_900 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_900 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-stop
d_exec'45'flat'45'stop_902 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'stop_902 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_904 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_904 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-sigop-halts
d_exec'45'sigop'45'halts_906 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 -> Bool
d_exec'45'sigop'45'halts_906 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts_906
du_exec'45'sigop'45'halts_906 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 -> Bool
du_exec'45'sigop'45'halts_906 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_3108
      v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_908 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 -> Bool
d_exec'45'sigop'45'halts'45'of_908 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts'45'of_908
du_exec'45'sigop'45'halts'45'of_908 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 -> Bool
du_exec'45'sigop'45'halts'45'of_908 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_3102
      v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_910 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_910 ~v0 ~v1 v2
  = du_exec'45'sigop'45'output'45'of_910 v2
du_exec'45'sigop'45'output'45'of_910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_910 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_3050
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-trace-halted
d_exec'45'trace'45'halted_912 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_912 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_914 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_914 ~v0 ~v1 ~v2
  = du_exec'45'trace'45'is'45'flat_914
du_exec'45'trace'45'is'45'flat_914 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_914 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'trace'45'is'45'flat_4498
      v0 v1 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.falloc
d_falloc_916 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_916 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fclosure
d_fclosure_918 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_918 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch
d_fetch_920 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
d_fetch_920 ~v0 ~v1 ~v2 = du_fetch_920
du_fetch_920 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
du_fetch_920 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-++-left
d_fetch'45''43''43''45'left_922 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'left_922 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-++-right
d_fetch'45''43''43''45'right_924 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'right_924 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-All
d_fetch'45'All_926 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_926 ~v0 ~v1 ~v2 = du_fetch'45'All_926
du_fetch'45'All_926 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_fetch'45'All_926 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_4190 v1 v2 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-Straight
d_fetch'45'Straight_928 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_928 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-dispatch
d_fetch'45'dispatch_930 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fetch'45'dispatch_930 ~v0 ~v1 v2 = du_fetch'45'dispatch_930 v2
du_fetch'45'dispatch_930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fetch'45'dispatch_930 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fetch'45'dispatch_3692
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-entry
d_find'45'entry_932 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Maybe Integer
d_find'45'entry_932 ~v0 ~v1 v2 = du_find'45'entry_932 v2
du_find'45'entry_932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Maybe Integer
du_find'45'entry_932 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'entry_228 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-entry-sound
d_find'45'entry'45'sound_934 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'entry'45'sound_934 ~v0 ~v1 v2
  = du_find'45'entry'45'sound_934 v2
du_find'45'entry'45'sound_934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'entry'45'sound_934 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'entry'45'sound_882
      (coe v0) v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-fn
d_find'45'fn_936 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> Maybe Integer
d_find'45'fn_936 ~v0 ~v1 v2 = du_find'45'fn_936 v2
du_find'45'fn_936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> Maybe Integer
du_find'45'fn_936 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-label
d_find'45'label_938 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_938 ~v0 ~v1 v2 = du_find'45'label_938 v2
du_find'45'label_938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_938 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-label-lands
d_find'45'label'45'lands_940 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_940 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-label-sound
d_find'45'label'45'sound_942 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_942 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-thunk
d_find'45'thunk_944 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_944 ~v0 ~v1 v2 = du_find'45'thunk_944 v2
du_find'45'thunk_944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_944 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-thunk-sound
d_find'45'thunk'45'sound_946 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_946 ~v0 ~v1 v2
  = du_find'45'thunk'45'sound_946 v2
du_find'45'thunk'45'sound_946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'sound_946 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk'45'sound_916
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-at
d_fl'45'at_948 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_948 ~v0 ~v1 v2 = du_fl'45'at_948 v2
du_fl'45'at_948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'at_948 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'at_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-at-++-miss
d_fl'45'at'45''43''43''45'miss_950 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'at'45''43''43''45'miss_950 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-go
d_fl'45'go_952 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_952 ~v0 ~v1 v2 = du_fl'45'go_952 v2
du_fl'45'go_952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'go_952 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-go-++-miss
d_fl'45'go'45''43''43''45'miss_954 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45''43''43''45'miss_954 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-go-lands
d_fl'45'go'45'lands_956 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_956 ~v0 ~v1 v2 = du_fl'45'go'45'lands_956 v2
du_fl'45'go'45'lands_956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_956 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'lands_3974
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-go-sound
d_fl'45'go'45'sound_958 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_958 ~v0 ~v1 v2 = du_fl'45'go'45'sound_958 v2
du_fl'45'go'45'sound_958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_958 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'sound_762
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-label-match
d_fl'45'label'45'match_960 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_960 ~v0 ~v1 v2
  = du_fl'45'label'45'match_960 v2
du_fl'45'label'45'match_960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'label'45'match_960 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-match-++-miss
d_fl'45'match'45''43''43''45'miss_962 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'match'45''43''43''45'miss_962 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-events
d_flat'45'events_964 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_flat'45'events_964 ~v0 ~v1 v2 = du_flat'45'events_964 v2
du_flat'45'events_964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_flat'45'events_964 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_510 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-events-[]
d_flat'45'events'45''91''93'_966 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_966 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-exec-instr
d_flat'45'exec'45'instr_968 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_968 ~v0 ~v1 v2
  = du_flat'45'exec'45'instr_968 v2
du_flat'45'exec'45'instr_968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_968 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-exec-instr-prefix
d_flat'45'exec'45'instr'45'prefix_970 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prefix_970 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-exec-instr-prog-irrelevant
d_flat'45'exec'45'instr'45'prog'45'irrelevant_972 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prog'45'irrelevant_972 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-halt
d_flat'45'halt_974 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'halt_974 ~v0 ~v1 ~v2 = du_flat'45'halt_974
du_flat'45'halt_974 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'halt_974
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'halt_1280
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-read-at
d_flat'45'read'45'at_976 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'at_976 ~v0 ~v1 ~v2 = du_flat'45'read'45'at_976
du_flat'45'read'45'at_976 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'at_976
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'at_110
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-read-tag
d_flat'45'read'45'tag_978 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_978 ~v0 ~v1 ~v2 = du_flat'45'read'45'tag_978
du_flat'45'read'45'tag_978 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_978
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-run
d_flat'45'run_980 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'run_980 ~v0 ~v1 = du_flat'45'run_980
du_flat'45'run_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'run_980
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_flat'45'run_2036
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-run-keeps-next-slot
d_flat'45'run'45'keeps'45'next'45'slot_982 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'run'45'keeps'45'next'45'slot_982 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-step-frame
d_flat'45'step'45'frame_984 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'frame_984 ~v0 ~v1 v2
  = du_flat'45'step'45'frame_984 v2
du_flat'45'step'45'frame_984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'frame_984 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'frame_1132
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-step-straight
d_flat'45'step'45'straight_986 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'straight_986 ~v0 ~v1 v2
  = du_flat'45'step'45'straight_986 v2
du_flat'45'step'45'straight_986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'straight_986 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flink
d_flink_988 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_988 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flink-do-branch
d_flink'45'do'45'branch_990 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch_990 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flink-do-jump
d_flink'45'do'45'jump_992 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'jump_992 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flink-do-ret
d_flink'45'do'45'ret_994 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'ret_994 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flinkView
d_flinkView_996 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3502
d_flinkView_996 ~v0 ~v1 ~v2 = du_flinkView_996
du_flinkView_996 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3502
du_flinkView_996
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flinkView_3530
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.floc
d_floc_998 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_floc_998 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.forced
d_forced_1000 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_forced_1000 ~v0 ~v1 ~v2 = du_forced_1000
du_forced_1000 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
du_forced_1000
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_4488
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fpc
d_fpc_1002 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1002 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fret
d_fret_1004 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1004 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.frontier-monotone
d_frontier'45'monotone_1006 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_frontier'45'monotone_1006 ~v0 ~v1 ~v2
  = du_frontier'45'monotone_1006
du_frontier'45'monotone_1006 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
du_frontier'45'monotone_1006 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_788
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-at
d_ft'45'at_1008 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'at_1008 ~v0 ~v1 v2 = du_ft'45'at_1008 v2
du_ft'45'at_1008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'at_1008 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'at_194 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-at-++-miss
d_ft'45'at'45''43''43''45'miss_1010 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45''43''43''45'miss_1010 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-at-prefix
d_ft'45'at'45'prefix_1012 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45'prefix_1012 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-go
d_ft'45'go_1014 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'go_1014 ~v0 ~v1 v2 = du_ft'45'go_1014 v2
du_ft'45'go_1014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'go_1014 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_192 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-go-++-miss
d_ft'45'go'45''43''43''45'miss_1016 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45''43''43''45'miss_1016 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-go-prefix
d_ft'45'go'45'prefix_1018 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45'prefix_1018 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-go-sound
d_ft'45'go'45'sound_1020 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_1020 ~v0 ~v1 v2 = du_ft'45'go'45'sound_1020 v2
du_ft'45'go'45'sound_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_1020 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_ft'45'go'45'sound_654
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-match
d_ft'45'match_1022 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'match_1022 ~v0 ~v1 v2 = du_ft'45'match_1022 v2
du_ft'45'match_1022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'match_1022 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_196 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-match-++-miss
d_ft'45'match'45''43''43''45'miss_1024 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45''43''43''45'miss_1024 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-match-prefix
d_ft'45'match'45'prefix_1026 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45'prefix_1026 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.grow-frame
d_grow'45'frame_1038 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_grow'45'frame_1038 ~v0 ~v1 v2 = du_grow'45'frame_1038 v2
du_grow'45'frame_1038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_grow'45'frame_1038 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_grow'45'frame_1268 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.inline-sv
d_inline'45'sv_1046 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_1046 ~v0 ~v1 ~v2 = du_inline'45'sv_1046
du_inline'45'sv_1046 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_1046 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_566
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ir-stable
d_ir'45'stable_1048 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_1048 v0 ~v1 v2 = du_ir'45'stable_1048 v0 v2
du_ir'45'stable_1048 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'stable_1048 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'stable_550
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_1050 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_1050 v0 ~v1 v2
  = du_ir'45'to'45'trace'45'slot'45'stable_1050 v0 v2
du_ir'45'to'45'trace'45'slot'45'stable_1050 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'slot'45'stable_1050 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_894
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.just-injℕ
d_just'45'injℕ_1052 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_1052 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.lab-eq
d_lab'45'eq_1054 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_1054 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.label-of?
d_label'45'of'63'_1056 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_1056 ~v0 ~v1 ~v2 = du_label'45'of'63'_1056
du_label'45'of'63'_1056 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_1056
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_122
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.label-of?-sound
d_label'45'of'63''45'sound_1058 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_1058 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame
d_leave'45'frame_1060 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_leave'45'frame_1060 ~v0 ~v1 ~v2 = du_leave'45'frame_1060
du_leave'45'frame_1060 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_leave'45'frame_1060
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_976
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-aux
d_leave'45'frame'45'aux_1062 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_leave'45'frame'45'aux_1062 ~v0 ~v1 ~v2
  = du_leave'45'frame'45'aux_1062
du_leave'45'frame'45'aux_1062 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_leave'45'frame'45'aux_1062
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_964
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-block-size
d_leave'45'frame'45'block'45'size_1064 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_1064 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_1066 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_1066 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_1068 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_1068 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_1070 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_1070 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_1072 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_1072 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_1074 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_1074 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_1076 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_1076 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.load-indirect-suc-twf
d_load'45'indirect'45'suc'45'twf_1078 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'twf_1078 ~v0 ~v1 ~v2
  = du_load'45'indirect'45'suc'45'twf_1078
du_load'45'indirect'45'suc'45'twf_1078 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'twf_1078 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'suc'45'twf_7934
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.load-indirect-twf
d_load'45'indirect'45'twf_1080 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'twf_1080 ~v0 ~v1 ~v2
  = du_load'45'indirect'45'twf_1080
du_load'45'indirect'45'twf_1080 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'twf_1080 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'twf_7916
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.log-abstract
d_log'45'abstract_1082 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'abstract_1082 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.log-of
d_log'45'of_1084 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'of_1084 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.log-pure
d_log'45'pure_1086 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'pure_1086 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.log-silent
d_log'45'silent_1088 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'silent_1088 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.log-step
d_log'45'step_1090 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'step_1090 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.mkFlat
d_mkFlat_1092 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_mkFlat_1092 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v0)
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.prim-sv
d_prim'45'sv_1096 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_1096 ~v0 ~v1 ~v2 = du_prim'45'sv_1096
du_prim'45'sv_1096 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_1096 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_548
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_1098 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_1098 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'aux_1098 v2
du_pure'45'sigop'45'out'45'aux_1098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'aux_1098 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_3014
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_1100 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_1100 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'val_1100 v2
du_pure'45'sigop'45'out'45'val_1100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_1100 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'val_2990
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.pure-sigop-output
d_pure'45'sigop'45'output_1102 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_1102 ~v0 ~v1 v2
  = du_pure'45'sigop'45'output_1102 v2
du_pure'45'sigop'45'output_1102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'output_1102 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_2984
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readLoc
d_readLoc_1118 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1118 ~v0 ~v1 ~v2 = du_readLoc_1118
du_readLoc_1118 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1118
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_1120 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_1120 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readReg-typed
d_readReg'45'typed_1122 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_1122 ~v0 ~v1 ~v2 = du_readReg'45'typed_1122
du_readReg'45'typed_1122 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_1122
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2744
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readTyped
d_readTyped_1124 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe AgdaAny
d_readTyped_1124 ~v0 ~v1 ~v2 = du_readTyped_1124
du_readTyped_1124 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe AgdaAny
du_readTyped_1124
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2800
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readTyped-adequate
d_readTyped'45'adequate_1126 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'adequate_1126 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readable-base
d_readable'45'base_1128 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850
d_readable'45'base_1128 ~v0 ~v1 ~v2 = du_readable'45'base_1128
du_readable'45'base_1128 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850
du_readable'45'base_1128
  = coe
      MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'45'base_880
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readable?
d_readable'63'_1130 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850
d_readable'63'_1130 ~v0 ~v1 ~v2 = du_readable'63'_1130
du_readable'63'_1130 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850
du_readable'63'_1130
  = coe
      MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'63'_892
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.reg-write-readLoc
d_reg'45'write'45'readLoc_1134 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_120 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'write'45'readLoc_1134 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.reloc-fetch
d_reloc'45'fetch_1136 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'fetch_1136 ~v0 ~v1 v2 = du_reloc'45'fetch_1136 v2
du_reloc'45'fetch_1136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'fetch_1136 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'fetch_3782 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.reloc-step
d_reloc'45'step_1138 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'step_1138 ~v0 ~v1 v2 = du_reloc'45'step_1138 v2
du_reloc'45'step_1138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'step_1138 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'step_3760 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.resultAt
d_resultAt_1144 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_resultAt_1144 ~v0 ~v1 = du_resultAt_1144
du_resultAt_1144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
du_resultAt_1144 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_resultAt_1176
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.retVal
d_retVal_1146 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> AgdaAny -> AgdaAny
d_retVal_1146 ~v0 ~v1 = du_retVal_1146
du_retVal_1146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> AgdaAny -> AgdaAny
du_retVal_1146 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_retVal_1224
      v0 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.runAt
d_runAt_1148 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runAt_1148 ~v0 ~v1 = du_runAt_1148
du_runAt_1148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runAt_1148 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_runAt_1160
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.runAt-≡
d_runAt'45''8801'_1150 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_runAt'45''8801'_1150 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shift
d_shift_1152 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_shift_1152 ~v0 ~v1 ~v2 = du_shift_1152
du_shift_1152 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_shift_1152
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shift_3428
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shift-loc
d_shift'45'loc_1154 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_1154 ~v0 ~v1 v2 = du_shift'45'loc_1154 v2
du_shift'45'loc_1154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_1154 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shift'45'loc_4356 (coe v0) v1
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-branch
d_shifted'45'branch_1156 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Bool ->
  Bool ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'branch_1156 ~v0 ~v1 ~v2 = du_shifted'45'branch_1156
du_shifted'45'branch_1156 ::
  Integer ->
  Bool ->
  Bool ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'branch_1156 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'branch_1854 v1 v4
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-call-at
d_shifted'45'call'45'at_1158 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'at_1158 ~v0 ~v1 ~v2
  = du_shifted'45'call'45'at_1158
du_shifted'45'call'45'at_1158 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'at_1158 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'at_1992 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-call-closure
d_shifted'45'call'45'closure_1160 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'closure_1160 ~v0 ~v1 v2
  = du_shifted'45'call'45'closure_1160 v2
du_shifted'45'call'45'closure_1160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'closure_1160 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'closure_2208
      (coe v0) v3 v4 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-call-code
d_shifted'45'call'45'code_1162 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'code_1162 ~v0 ~v1 v2
  = du_shifted'45'call'45'code_1162 v2
du_shifted'45'call'45'code_1162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'code_1162 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'code_2040
      (coe v0) v2 v4 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-call-sv
d_shifted'45'call'45'sv_1164 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'sv_1164 ~v0 ~v1 v2
  = du_shifted'45'call'45'sv_1164 v2
du_shifted'45'call'45'sv_1164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'sv_1164 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'sv_2122
      (coe v0) v2 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-eq
d_shifted'45'eq_1166 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shifted'45'eq_1166 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-frame
d_shifted'45'frame_1168 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'frame_1168 ~v0 ~v1 ~v2 = du_shifted'45'frame_1168
du_shifted'45'frame_1168 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'frame_1168 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'frame_1892 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-halt
d_shifted'45'halt_1170 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'halt_1170 ~v0 ~v1 ~v2 = du_shifted'45'halt_1170
du_shifted'45'halt_1170 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'halt_1170 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'halt_1958 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-instr
d_shifted'45'instr_1172 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'instr_1172 ~v0 ~v1 v2 = du_shifted'45'instr_1172 v2
du_shifted'45'instr_1172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'instr_1172 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'instr_2248
      (coe v0) v2 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-jump
d_shifted'45'jump_1174 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'jump_1174 ~v0 ~v1 ~v2 = du_shifted'45'jump_1174
du_shifted'45'jump_1174 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'jump_1174 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'jump_1796 v2 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-label
d_shifted'45'label_1176 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'label_1176 ~v0 ~v1 ~v2 = du_shifted'45'label_1176
du_shifted'45'label_1176 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'label_1176 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'label_1626 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-leave
d_shifted'45'leave_1178 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'leave_1178 ~v0 ~v1 ~v2 = du_shifted'45'leave_1178
du_shifted'45'leave_1178 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'leave_1178 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'leave_1652 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-ret
d_shifted'45'ret_1180 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret_1180 ~v0 ~v1 ~v2 = du_shifted'45'ret_1180
du_shifted'45'ret_1180 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret_1180 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret_1772 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-ret-aux
d_shifted'45'ret'45'aux_1182 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret'45'aux_1182 ~v0 ~v1 ~v2
  = du_shifted'45'ret'45'aux_1182
du_shifted'45'ret'45'aux_1182 ::
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret'45'aux_1182 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret'45'aux_1720 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-save-closure
d_shifted'45'save'45'closure_1184 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'save'45'closure_1184 ~v0 ~v1 ~v2
  = du_shifted'45'save'45'closure_1184
du_shifted'45'save'45'closure_1184 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'save'45'closure_1184 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'save'45'closure_1930
      v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-shift
d_shifted'45'shift_1186 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'shift_1186 ~v0 ~v1 ~v2 = du_shifted'45'shift_1186
du_shifted'45'shift_1186 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'shift_1186 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'shift_3442
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-straight
d_shifted'45'straight_1188 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'straight_1188 ~v0 ~v1 ~v2
  = du_shifted'45'straight_1188
du_shifted'45'straight_1188 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'straight_1188 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'straight_1590 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-thunk
d_shifted'45'thunk_1190 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'thunk_1190 ~v0 ~v1 ~v2 = du_shifted'45'thunk_1190
du_shifted'45'thunk_1190 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'thunk_1190 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'thunk_1682 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.step-at
d_step'45'at_1192 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_step'45'at_1192 ~v0 ~v1 ~v2 = du_step'45'at_1192
du_step'45'at_1192 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_step'45'at_1192 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366 v4
      v6 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.step-dispatch
d_step'45'dispatch_1194 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_step'45'dispatch_1194 ~v0 ~v1 v2 = du_step'45'dispatch_1194 v2
du_step'45'dispatch_1194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_step'45'dispatch_1194 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_step'45'dispatch_3690 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.stopsAt
d_stopsAt_1196 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> Bool
d_stopsAt_1196 ~v0 ~v1 = du_stopsAt_1196
du_stopsAt_1196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> Bool
du_stopsAt_1196 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_stopsAt_1184
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_1198 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_1198 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_1200 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_1200 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.sv-is-zero
d_sv'45'is'45'zero_1202 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_1202 ~v0 ~v1 ~v2 = du_sv'45'is'45'zero_1202
du_sv'45'is'45'zero_1202 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_1202
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.tag-zf
d_tag'45'zf_1204 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_1204 ~v0 ~v1 ~v2 = du_tag'45'zf_1204
du_tag'45'zf_1204 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_1204
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.thunk-of?
d_thunk'45'of'63'_1206 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_1206 ~v0 ~v1 ~v2 = du_thunk'45'of'63'_1206
du_thunk'45'of'63'_1206 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_1206
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63'_176
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.thunk-of?-sound
d_thunk'45'of'63''45'sound_1208 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_1208 ~v0 ~v1 ~v2
  = du_thunk'45'of'63''45'sound_1208
du_thunk'45'of'63''45'sound_1208 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_1208 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63''45'sound_620
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.thunk-part
d_thunk'45'part_1210 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'part_1210 ~v0 ~v1 ~v2 = du_thunk'45'part_1210
du_thunk'45'part_1210 ::
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'part_1210
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'part_172
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.valid-primitive-wf
d_valid'45'primitive'45'wf_1228 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_valid'45'primitive'45'wf_1228 ~v0 ~v1 ~v2
  = du_valid'45'primitive'45'wf_1228
du_valid'45'primitive'45'wf_1228 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
du_valid'45'primitive'45'wf_1228 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'primitive'45'wf_598
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_1234 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'frontier'45'advance_1234 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4408
      (coe v0) (coe v1) (coe v2) v4 v5 v6 v7 v8 v9 v11 v12 v13
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_1236 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'mem'45'preserved_1236 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                      v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5160
      (coe v0) (coe v1) (coe v2) v4 v5 v6 v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_1238 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'with'45'bf'45'transfer_1238 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'with'45'bf'45'transfer_4824
      (coe v0) (coe v1) (coe v2) v4 v5 v6 v7 v8 v9 v10 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.vr-mem-pres
d_vr'45'mem'45'pres_1240 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vr'45'mem'45'pres_1240 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ιᶠ
d_ι'7584'_1242 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
d_ι'7584'_1242 ~v0 ~v1 = du_ι'7584'_1242
du_ι'7584'_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
du_ι'7584'_1242
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_ι'7584'_1150
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.μ-layer-iso
d_μ'45'layer'45'iso_1244 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_μ'45'layer'45'iso_1244 ~v0 ~v1 = du_μ'45'layer'45'iso_1244
du_μ'45'layer'45'iso_1244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
du_μ'45'layer'45'iso_1244 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_μ'45'layer'45'iso_1948
      v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.≡ᵇ-true
d_'8801''7495''45'true_1246 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_1246 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlockRuns.closures
d_closures_1258 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closures_1258 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_closures_2592
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlockRuns.coalgs
d_coalgs_1260 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coalgs_1260 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_2594
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlockRuns.functions
d_functions_1262 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_functions_1262 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_functions_2596
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.bf-mono
d_bf'45'mono_1272 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'mono_1272 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_2474
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.cont-alloc
d_cont'45'alloc_1274 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_1274 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_2434
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.events
d_events_1276 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_1276 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.frame-pres
d_frame'45'pres_1278 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1278 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.live
d_live_1280 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1280 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.log
d_log_1282 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1282 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.mem-pres
d_mem'45'pres_1284 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_1284 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.no-link
d_no'45'link_1286 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1286 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.no-ret
d_no'45'ret_1288 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1288 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.out-mode
d_out'45'mode_1290 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1290 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_2432
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.place
d_place_1292 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_1292 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_2450
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.returned
d_returned_1294 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_1294 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.run
d_run_1296 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_1296 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_2436
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.settle
d_settle_1298 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1298 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_2430
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.steps
d_steps_1300 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  Integer
d_steps_1300 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2428
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.stops
d_stops_1302 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stops_1302 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_stops_2442
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.EnvType
d_EnvType_1312 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_1312 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_EnvType_1684
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.body
d_body_1314 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_body_1314 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body_1686
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.body-label
d_body'45'label_1316 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_1316 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'label_1690
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.code-ptr
d_code'45'ptr_1318 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1318 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.env
d_env_1320 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  AgdaAny
d_env_1320 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env_1688 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.env-at
d_env'45'at_1322 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616
d_env'45'at_1322 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'at_1694
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_1324 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_1324 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.loc-mode
d_loc'45'mode_1326 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  AgdaAny
d_loc'45'mode_1326 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_loc'45'mode_1692
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_1328 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_sucLoc'45'before_1328 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1698
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.falloc
d_falloc_1338 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_1338 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.fclosure
d_fclosure_1340 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1340 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.flink
d_flink_1342 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1342 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.floc
d_floc_1344 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_floc_1344 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.fpc
d_fpc_1346 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1346 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.fret
d_fret_1348 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1348 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.MachineRefinesObsF.traces-agree
d_traces'45'agree_1384 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1384 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.MachineRefinesObsF.value-realized
d_value'45'realized_1386 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102
d_value'45'realized_1386 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_2316
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.PairValidWF.fst-cell
d_fst'45'cell_1390 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578
d_fst'45'cell_1390 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1896
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.PairValidWF.snd-cell
d_snd'45'cell_1392 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578
d_snd'45'cell_1392 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1898
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.PairValidWF.sucLoc-before
d_sucLoc'45'before_1394 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_sucLoc'45'before_1394 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1894
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.at-end
d_at'45'end_1448 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1448 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.bf-mono
d_bf'45'mono_1450 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'mono_1450 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_2214
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.cont-alloc
d_cont'45'alloc_1452 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_1452 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_2178
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.frame-pres
d_frame'45'pres_1454 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1454 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.heap-pres
d_heap'45'pres_1456 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_1456 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.live
d_live_1458 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1458 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.log
d_log_1460 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1460 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.no-link
d_no'45'link_1462 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1462 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.no-ret
d_no'45'ret_1464 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1464 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.out-mode
d_out'45'mode_1466 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1466 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_2176
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.place
d_place_1468 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_1468 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_2196
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.run
d_run_1470 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_1470 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_2180
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.settle
d_settle_1472 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1472 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_2174
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.stack-pres
d_stack'45'pres_1474 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_1474 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.steps
d_steps_1476 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  Integer
d_steps_1476 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2172
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.stops
d_stops_1478 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stops_1478 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_stops_2186
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_1482 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SMPrimitives.instr-writes-slot
d_instr'45'writes'45'slot_1484 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe Integer
d_instr'45'writes'45'slot_1484 ~v0 ~v1
  = du_instr'45'writes'45'slot_1484
du_instr'45'writes'45'slot_1484 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe Integer
du_instr'45'writes'45'slot_1484
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_instr'45'writes'45'slot_692
-- Once.CCC.Codegen.IRObsCorrect.Machine._._+_
d__'43'__1564 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> Integer
d__'43'__1564 ~v0 ~v1 = du__'43'__1564
du__'43'__1564 :: Integer -> Integer -> Integer
du__'43'__1564 = coe addInt
-- Once.CCC.Codegen.IRObsCorrect.Machine._._++_
d__'43''43'__1566 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d__'43''43'__1566 ~v0 ~v1 = du__'43''43'__1566
du__'43''43'__1566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'43''43'__1566 v0 v1 v2 v3
  = coe MAlonzo.Code.Data.List.Base.du__'43''43'__32 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._._<_
d__'60'__1570 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> ()
d__'60'__1570 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._._×_
d__'215'__1572 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'__1572 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._._-_
d__'45'__1578 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> Integer
d__'45'__1578 ~v0 ~v1 = du__'45'__1578
du__'45'__1578 :: Integer -> Integer -> Integer
du__'45'__1578 = coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
-- Once.CCC.Codegen.IRObsCorrect.Machine._._≡_
d__'8801'__1580 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._._≢_
d__'8802'__1582 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> ()
d__'8802'__1582 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._._≤_
d__'8804'__1584 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.++-assoc
d_'43''43''45'assoc_1586 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'assoc_1586 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.++⁺
d_'43''43''8314'_1588 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_'43''43''8314'_1588 ~v0 ~v1 = du_'43''43''8314'_1588
du_'43''43''8314'_1588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_'43''43''8314'_1588 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      v4 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.++⁻
d_'43''43''8315'_1590 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''43''8315'_1590 ~v0 ~v1 = du_'43''43''8315'_1590
du_'43''43''8315'_1590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'43''43''8315'_1590 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
      v4 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.+-assoc
d_'43''45'assoc_1592 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_1592 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.+-comm
d_'43''45'comm_1594 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_1594 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.+-identityʳ
d_'43''45'identity'691'_1596 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691'_1596 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.+-suc
d_'43''45'suc_1598 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'suc_1598 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.<-irrefl
d_'60''45'irrefl_1600 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_1600 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.<-trans
d_'60''45'trans_1602 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans_1602 ~v0 ~v1 = du_'60''45'trans_1602
du_'60''45'trans_1602 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'trans_1602 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122 v1 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.<-≤-trans
d_'60''45''8804''45'trans_1604 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45''8804''45'trans_1604 ~v0 ~v1
  = du_'60''45''8804''45'trans_1604
du_'60''45''8804''45'trans_1604 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45''8804''45'trans_1604 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.All
d_All_1606 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AllocMode
d_AllocMode_1608 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FitsInReg
d_FitsInReg_1616 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FitsInRegI
d_FitsInRegI_1618 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.IR
d_IR_1622 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.List
d_List_1628 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Maybe
d_Maybe_1630 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Type
d_Type_1638 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.case_of_
d_case_of__1648 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_case_of__1648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_case_of__1648 v6 v7
du_case_of__1648 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_case_of__1648 v0 v1 = coe v1 v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.cong
d_cong_1650 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_1650 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.cong₂
d_cong'8322'_1652 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8322'_1652 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.fits-in-reg?
d_fits'45'in'45'reg'63'_1664 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24
d_fits'45'in'45'reg'63'_1664 ~v0 ~v1
  = du_fits'45'in'45'reg'63'_1664
du_fits'45'in'45'reg'63'_1664 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24
du_fits'45'in'45'reg'63'_1664
  = coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_32
-- Once.CCC.Codegen.IRObsCorrect.Machine._.length
d_length_1684 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer
d_length_1684 ~v0 ~v1 = du_length_1684
du_length_1684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer
du_length_1684 v0 v1
  = coe MAlonzo.Code.Data.List.Base.du_length_268
-- Once.CCC.Codegen.IRObsCorrect.Machine._.length-++
d_length'45''43''43'_1686 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''43''43'_1686 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.map
d_map_1688 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_map_1688 ~v0 ~v1 = du_map_1688
du_map_1688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_map_1688 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Data.List.Base.du_map_22 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.map
d_map_1690 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_map_1690 ~v0 ~v1 = du_map_1690
du_map_1690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_map_1690 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Data.Maybe.Base.du_map_64 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.m≤m+n
d_m'8804'm'43'n_1692 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'm'43'n_1692 ~v0 ~v1 = du_m'8804'm'43'n_1692
du_m'8804'm'43'n_1692 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'm'43'n_1692 v0 v1
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.m≤n+m
d_m'8804'n'43'm_1694 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43'm_1694 ~v0 ~v1 = du_m'8804'n'43'm_1694
du_m'8804'n'43'm_1694 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'43'm_1694 v0 v1
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636 v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.n<1+n
d_n'60'1'43'n_1696 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'1'43'n_1696 ~v0 ~v1 = du_n'60'1'43'n_1696
du_n'60'1'43'n_1696 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'60'1'43'n_1696
  = coe MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
-- Once.CCC.Codegen.IRObsCorrect.Machine._.n≤1+n
d_n'8804'1'43'n_1700 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'1'43'n_1700 ~v0 ~v1 = du_n'8804'1'43'n_1700
du_n'8804'1'43'n_1700 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'8804'1'43'n_1700
  = coe MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
-- Once.CCC.Codegen.IRObsCorrect.Machine._.fst
d_fst_1704 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_1704 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.snd
d_snd_1706 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_1706 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.subst
d_subst_1712 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_subst_1712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_subst_1712 v9
du_subst_1712 :: AgdaAny -> AgdaAny
du_subst_1712 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.subst₂
d_subst'8322'_1714 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_subst'8322'_1714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 ~v13 v14
  = du_subst'8322'_1714 v14
du_subst'8322'_1714 :: AgdaAny -> AgdaAny
du_subst'8322'_1714 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.sym
d_sym_1718 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1718 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.take
d_take_1720 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> [AgdaAny] -> [AgdaAny]
d_take_1720 ~v0 ~v1 = du_take_1720
du_take_1720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> [AgdaAny] -> [AgdaAny]
du_take_1720 v0 v1 v2 v3
  = coe MAlonzo.Code.Data.List.Base.du_take_530 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.trans
d_trans_1724 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1724 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Nat
d_Nat_1732 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Int
d_Int_1734 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.∃
d_'8707'_1736 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> ()
d_'8707'_1736 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.∃-syntax
d_'8707''45'syntax_1738 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> ()
d_'8707''45'syntax_1738 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.≤-<-trans
d_'8804''45''60''45'trans_1740 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45''60''45'trans_1740 ~v0 ~v1
  = du_'8804''45''60''45'trans_1740
du_'8804''45''60''45'trans_1740 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45''60''45'trans_1740 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.≤-refl
d_'8804''45'refl_1742 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'refl_1742 ~v0 ~v1 = du_'8804''45'refl_1742
du_'8804''45'refl_1742 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'refl_1742
  = coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
-- Once.CCC.Codegen.IRObsCorrect.Machine._.≤-reflexive
d_'8804''45'reflexive_1744 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'reflexive_1744 ~v0 ~v1 = du_'8804''45'reflexive_1744
du_'8804''45'reflexive_1744 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'reflexive_1744 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896 v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.≤-trans
d_'8804''45'trans_1746 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'trans_1746 ~v0 ~v1 = du_'8804''45'trans_1746
du_'8804''45'trans_1746 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'trans_1746 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⊥
d_'8869'_1748 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> ()
d_'8869'_1748 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⊥-elim
d_'8869''45'elim_1750 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim_1750 ~v0 ~v1 = du_'8869''45'elim_1750
du_'8869''45'elim_1750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
du_'8869''45'elim_1750 v0 v1 v2
  = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⌊_⌋
d_'8970'_'8971'_1752 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_'8970'_'8971'_1752 ~v0 ~v1 = du_'8970'_'8971'_1752
du_'8970'_'8971'_1752 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
du_'8970'_'8971'_1752
  = coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_1754 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_1754 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.ChainNotNested
d_ChainNotNested_1794 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 -> ()
d_ChainNotNested_1794 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.NotNested
d_NotNested_1796 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> ()
d_NotNested_1796 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events
d_chain'45'events_1798 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_chain'45'events_1798 ~v0 ~v1 = du_chain'45'events_1798
du_chain'45'events_1798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_chain'45'events_1798 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_650 v0 v1
      v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-++
d_chain'45'events'45''43''43'_1800 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_1800 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-len0
d_chain'45'events'45'len0_1802 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'len0_1802 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-nil
d_chain'45'events'45'nil_1804 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_1804 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-subst
d_chain'45'events'45'subst_1806 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst_1806 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-subst-len
d_chain'45'events'45'subst'45'len_1808 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'len_1808 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-subst-start
d_chain'45'events'45'subst'45'start_1810 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_1810 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-left
d_chain'45'left_1812 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'left_1812 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-left-at
d_chain'45'left'45'at_1814 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'left'45'at_1814 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-log
d_chain'45'log_1816 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'log_1816 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.ev-of-loc
d_ev'45'of'45'loc_1818 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_ev'45'of'45'loc_1818 ~v0 ~v1 = du_ev'45'of'45'loc_1818
du_ev'45'of'45'loc_1818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_ev'45'of'45'loc_1818 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_ev'45'of'45'loc_498 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.event-of
d_event'45'of_1820 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_event'45'of_1820 ~v0 ~v1 = du_event'45'of_1820
du_event'45'of_1820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_event'45'of_1820 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_504 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events
d_flat'45'events_1822 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_flat'45'events_1822 ~v0 ~v1 = du_flat'45'events_1822
du_flat'45'events_1822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_flat'45'events_1822
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_510
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-[]
d_flat'45'events'45''91''93'_1824 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_1824 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-fetch
d_flat'45'events'45'fetch_1826 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_flat'45'events'45'fetch_1826 ~v0 ~v1
  = du_flat'45'events'45'fetch_1826
du_flat'45'events'45'fetch_1826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_flat'45'events'45'fetch_1826
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'fetch_514
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-halted
d_flat'45'events'45'halted_1828 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'halted_1828 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-reify
d_flat'45'events'45'reify_1830 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_854 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'reify_1830 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-settled
d_flat'45'events'45'settled_1832 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'settled_1832 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-step
d_flat'45'events'45'step_1834 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_flat'45'events'45'step_1834 ~v0 ~v1
  = du_flat'45'events'45'step_1834
du_flat'45'events'45'step_1834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_flat'45'events'45'step_1834
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'step_512
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-steps
d_flat'45'events'45'steps_1836 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'steps_1836 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.step-log
d_step'45'log_1838 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'log_1838 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.AllSlotStable
d_AllSlotStable_1938 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_AllSlotStable_1938 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BeforeFrontier
d_BeforeFrontier_1940 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlockAt
d_BlockAt_1942 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockAt_1942 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlockRuns
d_BlockRuns_1944 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlocksAt
d_BlocksAt_1948 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_BlocksAt_1948 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CallPost
d_CallPost_1950 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun
d_CalleeRun_1952 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRuns
d_CalleeRuns_1956 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_CalleeRuns_1956 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CellAt
d_CellAt_1958 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CoalgRuns
d_CoalgRuns_1960 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_CoalgRuns_1960 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.EnvAt
d_EnvAt_1962 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState
d_FlatState_1964 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatSteps
d_FlatSteps_1968 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatSteps-++
d_FlatSteps'45''43''43'_1970 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_FlatSteps'45''43''43'_1970 ~v0 ~v1 ~v2
  = du_FlatSteps'45''43''43'_1970
du_FlatSteps'45''43''43'_1970 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_FlatSteps'45''43''43'_1970 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1170
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatSteps-prefix
d_FlatSteps'45'prefix_1972 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_FlatSteps'45'prefix_1972 ~v0 ~v1 ~v2
  = du_FlatSteps'45'prefix_1972
du_FlatSteps'45'prefix_1972 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_FlatSteps'45'prefix_1972 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'prefix_998
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatSteps-reloc
d_FlatSteps'45'reloc_1974 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_FlatSteps'45'reloc_1974 ~v0 ~v1 ~v2 = du_FlatSteps'45'reloc_1974
du_FlatSteps'45'reloc_1974 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_FlatSteps'45'reloc_1974 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'reloc_1040
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlinkView
d_FlinkView_1976 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FnRuns
d_FnRuns_1978 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_FnRuns_1978 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.IRObsCorrectF
d_IRObsCorrectF_1980 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_1980 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.InlineRep
d_InlineRep_1982 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.InputAt
d_InputAt_1984 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.InstrWF
d_InstrWF_1986 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> ()
d_InstrWF_1986 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.LabelsAt
d_LabelsAt_1988 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_LabelsAt_1988 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.MachineRefinesObsF
d_MachineRefinesObsF_1990 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ProgFree
d_ProgFree_1994 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> ()
d_ProgFree_1994 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.Readable
d_Readable_1996 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ResultPlace
d_ResultPlace_1998 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.Shifted
d_Shifted_2000 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Shifted_2000 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.SpanAt
d_SpanAt_2002 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_SpanAt_2002 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.Straight
d_Straight_2004 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_Straight_2004 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.StraightStep
d_StraightStep_2006 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> ()
d_StraightStep_2006 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValidAtWF
d_ValidAtWF_2008 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized
d_ValueRealized_2010 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.blocks
d_blocks_2020 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_2020 v0 ~v1 ~v2 = du_blocks_2020 v0
du_blocks_2020 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_blocks_2020 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_1978
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.callView
d_callView_2022 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350
d_callView_2022 ~v0 ~v1 v2 = du_callView_2022 v2
du_callView_2022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350
du_callView_2022 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1368 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.cata-correct
d_cata'45'correct_2026 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286) ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286
d_cata'45'correct_2026 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cata'45'correct_2642
      v0 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.chain-events
d_chain'45'events_2032 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_chain'45'events_2032 ~v0 ~v1 v2 = du_chain'45'events_2032 v2
du_chain'45'events_2032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_chain'45'events_2032 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_650
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.chain-events-++
d_chain'45'events'45''43''43'_2034 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_2034 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.chain-events-nil
d_chain'45'events'45'nil_2036 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_2036 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.chain-events-subst-start
d_chain'45'events'45'subst'45'start_2038 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_2038 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.chain-left
d_chain'45'left_2040 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'left_2040 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.decomposeClosureWF
d_decomposeClosureWF_2046 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650
d_decomposeClosureWF_2046 ~v0 ~v1 ~v2 = du_decomposeClosureWF_2046
du_decomposeClosureWF_2046 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650
du_decomposeClosureWF_2046 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1720
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.decomposePairWF
d_decomposePairWF_2048 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874
d_decomposePairWF_2048 ~v0 ~v1 ~v2 = du_decomposePairWF_2048
du_decomposePairWF_2048 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874
du_decomposePairWF_2048 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1916
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-branch
d_do'45'branch_2050 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_2050 ~v0 ~v1 v2 = du_do'45'branch_2050 v2
du_do'45'branch_2050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch_2050 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_938 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-branch-at
d_do'45'branch'45'at_2052 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch'45'at_2052 ~v0 ~v1 ~v2 = du_do'45'branch'45'at_2052
du_do'45'branch'45'at_2052 ::
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch'45'at_2052
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'branch'45'at_930
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call
d_do'45'call_2054 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_2054 ~v0 ~v1 v2 = du_do'45'call_2054 v2
du_do'45'call_2054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call_2054 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-at
d_do'45'call'45'at_2056 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_2056 ~v0 ~v1 v2 = du_do'45'call'45'at_2056 v2
du_do'45'call'45'at_2056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'at_2056 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1284 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-code
d_do'45'call'45'code_2058 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'code_2058 ~v0 ~v1 v2
  = du_do'45'call'45'code_2058 v2
du_do'45'call'45'code_2058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'code_2058 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'code_1292
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-code-prefix
d_do'45'call'45'code'45'prefix_2060 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'code'45'prefix_2060 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-prefix
d_do'45'call'45'prefix_2062 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'prefix_2062 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-sv
d_do'45'call'45'sv_2064 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'sv_2064 ~v0 ~v1 v2 = du_do'45'call'45'sv_2064 v2
du_do'45'call'45'sv_2064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'sv_2064 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'sv_1316 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-sv-prefix
d_do'45'call'45'sv'45'prefix_2066 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'sv'45'prefix_2066 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-jump
d_do'45'jump_2068 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_2068 ~v0 ~v1 ~v2 = du_do'45'jump_2068
du_do'45'jump_2068 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_2068
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_922
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret
d_do'45'ret_2070 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_2070 ~v0 ~v1 ~v2 = du_do'45'ret_2070
du_do'45'ret_2070 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_2070
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_1140
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-alloc
d_do'45'ret'45'alloc_2072 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_2072 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_2074 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_2074 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_2076 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_2076 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_2078 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_2078 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_2080 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_2080 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-save-closure
d_do'45'save'45'closure_2082 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'save'45'closure_2082 ~v0 ~v1 ~v2
  = du_do'45'save'45'closure_2082
du_do'45'save'45'closure_2082 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'save'45'closure_2082
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1498
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-thunk
d_do'45'thunk_2084 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_2084 ~v0 ~v1 v2 = du_do'45'thunk_2084 v2
du_do'45'thunk_2084 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_2084 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1274 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.emitted
d_emitted_2086 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_emitted_2086 v0 ~v1 ~v2 = du_emitted_2086 v0
du_emitted_2086 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_emitted_2086 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_1966
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.enter-call
d_enter'45'call_2088 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_enter'45'call_2088 ~v0 ~v1 v2 = du_enter'45'call_2088 v2
du_enter'45'call_2088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'call_2088 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.enter-frame
d_enter'45'frame_2090 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_enter'45'frame_2090 ~v0 ~v1 v2 = du_enter'45'frame_2090 v2
du_enter'45'frame_2090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'frame_2090 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'frame_954 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.entry-flat
d_entry'45'flat_2092 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_entry'45'flat_2092 ~v0 ~v1 ~v2 = du_entry'45'flat_2092
du_entry'45'flat_2092 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_entry'45'flat_2092
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_entry'45'flat_1986
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.entry-of?
d_entry'45'of'63'_2094 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
d_entry'45'of'63'_2094 ~v0 ~v1 ~v2 = du_entry'45'of'63'_2094
du_entry'45'of'63'_2094 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
du_entry'45'of'63'_2094
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63'_168
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.entry-of?-sound
d_entry'45'of'63''45'sound_2096 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'of'63''45'sound_2096 ~v0 ~v1 ~v2
  = du_entry'45'of'63''45'sound_2096
du_entry'45'of'63''45'sound_2096 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'of'63''45'sound_2096 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63''45'sound_634
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.entry→thunk
d_entry'8594'thunk_2098 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8594'thunk_2098 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.evalᴰ
d_eval'7472'_2104 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_eval'7472'_2104 ~v0 v1 v2 = du_eval'7472'_2104 v1 v2
du_eval'7472'_2104 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
du_eval'7472'_2104 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_1156
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.event-of
d_event'45'of_2106 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_event'45'of_2106 ~v0 ~v1 ~v2 = du_event'45'of_2106
du_event'45'of_2106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_event'45'of_2106
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_504
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.eventsAt
d_eventsAt_2108 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_eventsAt_2108 ~v0 ~v1 v2 = du_eventsAt_2108 v2
du_eventsAt_2108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_eventsAt_2108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eventsAt_1168
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract
d_exec'45'abstract_2110 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2110 ~v0 ~v1 v2 = du_exec'45'abstract_2110 v2
du_exec'45'abstract_2110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_2110 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3210
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-load-indirect-output
d_exec'45'abstract'45'load'45'indirect'45'output_2112 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'output_2112 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-load-indirect-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_2114 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_2114
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-load-indirect-suc-output
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_2116 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_2116
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-load-indirect-suc-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_2118 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_2118
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_2120 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_2120 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-halted-WF
d_exec'45'abstract'45'preserves'45'halted'45'WF_2122 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted'45'WF_2122 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-heap-ref
d_exec'45'abstract'45'preserves'45'heap'45'ref_2124 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heap'45'ref_2124 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_2126 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_2126 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_2128 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_2128 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat
d_exec'45'flat_2130 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_2130 ~v0 ~v1 v2 = du_exec'45'flat_2130 v2
du_exec'45'flat_2130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_exec'45'flat_2130 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3688 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-halted
d_exec'45'flat'45'halted_2132 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_2132 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-invariant
d_exec'45'flat'45'invariant_2134 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_2134 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-keeps-next-slot
d_exec'45'flat'45'keeps'45'next'45'slot_2136 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'keeps'45'next'45'slot_2136 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-offend
d_exec'45'flat'45'offend_2138 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_2138 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-reloc
d_exec'45'flat'45'reloc_2140 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'flat'45'reloc_2140 ~v0 ~v1 v2
  = du_exec'45'flat'45'reloc_2140 v2
du_exec'45'flat'45'reloc_2140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'flat'45'reloc_2140 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'flat'45'reloc_3738
      (coe v0) v1 v2 v3 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-step
d_exec'45'flat'45'step_2142 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_2142 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-steps
d_exec'45'flat'45'steps_2144 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_2144 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-stop
d_exec'45'flat'45'stop_2146 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'stop_2146 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_2148 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_2148 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-sigop-halts
d_exec'45'sigop'45'halts_2150 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 -> Bool
d_exec'45'sigop'45'halts_2150 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts_2150
du_exec'45'sigop'45'halts_2150 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 -> Bool
du_exec'45'sigop'45'halts_2150 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_3108
      v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2152 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 -> Bool
d_exec'45'sigop'45'halts'45'of_2152 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts'45'of_2152
du_exec'45'sigop'45'halts'45'of_2152 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 -> Bool
du_exec'45'sigop'45'halts'45'of_2152 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_3102
      v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2154 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_2154 ~v0 ~v1 v2
  = du_exec'45'sigop'45'output'45'of_2154 v2
du_exec'45'sigop'45'output'45'of_2154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_2154 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_3050
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-trace-halted
d_exec'45'trace'45'halted_2156 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_2156 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_2158 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_2158 ~v0 ~v1 ~v2
  = du_exec'45'trace'45'is'45'flat_2158
du_exec'45'trace'45'is'45'flat_2158 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_2158 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'trace'45'is'45'flat_4498
      v0 v1 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch
d_fetch_2164 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
d_fetch_2164 ~v0 ~v1 ~v2 = du_fetch_2164
du_fetch_2164 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
du_fetch_2164 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-++-left
d_fetch'45''43''43''45'left_2166 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'left_2166 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-++-right
d_fetch'45''43''43''45'right_2168 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'right_2168 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-All
d_fetch'45'All_2170 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_2170 ~v0 ~v1 ~v2 = du_fetch'45'All_2170
du_fetch'45'All_2170 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_fetch'45'All_2170 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_4190 v1 v2 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-Straight
d_fetch'45'Straight_2172 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_2172 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-dispatch
d_fetch'45'dispatch_2174 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fetch'45'dispatch_2174 ~v0 ~v1 v2 = du_fetch'45'dispatch_2174 v2
du_fetch'45'dispatch_2174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fetch'45'dispatch_2174 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fetch'45'dispatch_3692
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-entry
d_find'45'entry_2176 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Maybe Integer
d_find'45'entry_2176 ~v0 ~v1 v2 = du_find'45'entry_2176 v2
du_find'45'entry_2176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Maybe Integer
du_find'45'entry_2176 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'entry_228 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-entry-sound
d_find'45'entry'45'sound_2178 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'entry'45'sound_2178 ~v0 ~v1 v2
  = du_find'45'entry'45'sound_2178 v2
du_find'45'entry'45'sound_2178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'entry'45'sound_2178 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'entry'45'sound_882
      (coe v0) v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-fn
d_find'45'fn_2180 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> Maybe Integer
d_find'45'fn_2180 ~v0 ~v1 v2 = du_find'45'fn_2180 v2
du_find'45'fn_2180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> Maybe Integer
du_find'45'fn_2180 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-label
d_find'45'label_2182 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_2182 ~v0 ~v1 v2 = du_find'45'label_2182 v2
du_find'45'label_2182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_2182 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-label-lands
d_find'45'label'45'lands_2184 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_2184 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-label-sound
d_find'45'label'45'sound_2186 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_2186 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-thunk
d_find'45'thunk_2188 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_2188 ~v0 ~v1 v2 = du_find'45'thunk_2188 v2
du_find'45'thunk_2188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_2188 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-thunk-sound
d_find'45'thunk'45'sound_2190 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_2190 ~v0 ~v1 v2
  = du_find'45'thunk'45'sound_2190 v2
du_find'45'thunk'45'sound_2190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'sound_2190 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk'45'sound_916
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-at
d_fl'45'at_2192 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_2192 ~v0 ~v1 v2 = du_fl'45'at_2192 v2
du_fl'45'at_2192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'at_2192 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'at_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-at-++-miss
d_fl'45'at'45''43''43''45'miss_2194 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'at'45''43''43''45'miss_2194 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-go
d_fl'45'go_2196 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_2196 ~v0 ~v1 v2 = du_fl'45'go_2196 v2
du_fl'45'go_2196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'go_2196 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-go-++-miss
d_fl'45'go'45''43''43''45'miss_2198 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45''43''43''45'miss_2198 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-go-lands
d_fl'45'go'45'lands_2200 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_2200 ~v0 ~v1 v2 = du_fl'45'go'45'lands_2200 v2
du_fl'45'go'45'lands_2200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_2200 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'lands_3974
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-go-sound
d_fl'45'go'45'sound_2202 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_2202 ~v0 ~v1 v2 = du_fl'45'go'45'sound_2202 v2
du_fl'45'go'45'sound_2202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_2202 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'sound_762
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-label-match
d_fl'45'label'45'match_2204 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_2204 ~v0 ~v1 v2
  = du_fl'45'label'45'match_2204 v2
du_fl'45'label'45'match_2204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'label'45'match_2204 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-match-++-miss
d_fl'45'match'45''43''43''45'miss_2206 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'match'45''43''43''45'miss_2206 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-events
d_flat'45'events_2208 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_flat'45'events_2208 ~v0 ~v1 v2 = du_flat'45'events_2208 v2
du_flat'45'events_2208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_flat'45'events_2208 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_510 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-events-[]
d_flat'45'events'45''91''93'_2210 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_2210 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-exec-instr
d_flat'45'exec'45'instr_2212 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_2212 ~v0 ~v1 v2
  = du_flat'45'exec'45'instr_2212 v2
du_flat'45'exec'45'instr_2212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_2212 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-exec-instr-prefix
d_flat'45'exec'45'instr'45'prefix_2214 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prefix_2214 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-exec-instr-prog-irrelevant
d_flat'45'exec'45'instr'45'prog'45'irrelevant_2216 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prog'45'irrelevant_2216 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-halt
d_flat'45'halt_2218 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'halt_2218 ~v0 ~v1 ~v2 = du_flat'45'halt_2218
du_flat'45'halt_2218 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'halt_2218
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'halt_1280
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-read-at
d_flat'45'read'45'at_2220 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'at_2220 ~v0 ~v1 ~v2 = du_flat'45'read'45'at_2220
du_flat'45'read'45'at_2220 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'at_2220
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'at_110
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-read-tag
d_flat'45'read'45'tag_2222 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_2222 ~v0 ~v1 ~v2
  = du_flat'45'read'45'tag_2222
du_flat'45'read'45'tag_2222 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_2222
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-run
d_flat'45'run_2224 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'run_2224 ~v0 ~v1 v2 = du_flat'45'run_2224 v2
du_flat'45'run_2224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'run_2224 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_flat'45'run_2036
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-run-keeps-next-slot
d_flat'45'run'45'keeps'45'next'45'slot_2226 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'run'45'keeps'45'next'45'slot_2226 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-step-frame
d_flat'45'step'45'frame_2228 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'frame_2228 ~v0 ~v1 v2
  = du_flat'45'step'45'frame_2228 v2
du_flat'45'step'45'frame_2228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'frame_2228 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'frame_1132
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-step-straight
d_flat'45'step'45'straight_2230 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'straight_2230 ~v0 ~v1 v2
  = du_flat'45'step'45'straight_2230 v2
du_flat'45'step'45'straight_2230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'straight_2230 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flink-do-branch
d_flink'45'do'45'branch_2234 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch_2234 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flink-do-jump
d_flink'45'do'45'jump_2236 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'jump_2236 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flink-do-ret
d_flink'45'do'45'ret_2238 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'ret_2238 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flinkView
d_flinkView_2240 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3502
d_flinkView_2240 ~v0 ~v1 ~v2 = du_flinkView_2240
du_flinkView_2240 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3502
du_flinkView_2240
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flinkView_3530
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.forced
d_forced_2244 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_forced_2244 ~v0 ~v1 ~v2 = du_forced_2244
du_forced_2244 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
du_forced_2244
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_4488
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.frontier-monotone
d_frontier'45'monotone_2250 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_frontier'45'monotone_2250 ~v0 ~v1 ~v2
  = du_frontier'45'monotone_2250
du_frontier'45'monotone_2250 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
du_frontier'45'monotone_2250 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_788
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-at
d_ft'45'at_2252 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'at_2252 ~v0 ~v1 v2 = du_ft'45'at_2252 v2
du_ft'45'at_2252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'at_2252 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'at_194 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-at-++-miss
d_ft'45'at'45''43''43''45'miss_2254 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45''43''43''45'miss_2254 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-at-prefix
d_ft'45'at'45'prefix_2256 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45'prefix_2256 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-go
d_ft'45'go_2258 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'go_2258 ~v0 ~v1 v2 = du_ft'45'go_2258 v2
du_ft'45'go_2258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'go_2258 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_192 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-go-++-miss
d_ft'45'go'45''43''43''45'miss_2260 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45''43''43''45'miss_2260 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-go-prefix
d_ft'45'go'45'prefix_2262 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45'prefix_2262 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-go-sound
d_ft'45'go'45'sound_2264 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_2264 ~v0 ~v1 v2 = du_ft'45'go'45'sound_2264 v2
du_ft'45'go'45'sound_2264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_2264 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_ft'45'go'45'sound_654
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-match
d_ft'45'match_2266 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'match_2266 ~v0 ~v1 v2 = du_ft'45'match_2266 v2
du_ft'45'match_2266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'match_2266 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_196 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-match-++-miss
d_ft'45'match'45''43''43''45'miss_2268 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45''43''43''45'miss_2268 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-match-prefix
d_ft'45'match'45'prefix_2270 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45'prefix_2270 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.grow-frame
d_grow'45'frame_2282 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_grow'45'frame_2282 ~v0 ~v1 v2 = du_grow'45'frame_2282 v2
du_grow'45'frame_2282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_grow'45'frame_2282 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_grow'45'frame_1268 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.inline-sv
d_inline'45'sv_2290 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_2290 ~v0 ~v1 ~v2 = du_inline'45'sv_2290
du_inline'45'sv_2290 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_2290 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_566
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ir-stable
d_ir'45'stable_2292 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_2292 v0 ~v1 v2 = du_ir'45'stable_2292 v0 v2
du_ir'45'stable_2292 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'stable_2292 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'stable_550
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_2294 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_2294 v0 ~v1 v2
  = du_ir'45'to'45'trace'45'slot'45'stable_2294 v0 v2
du_ir'45'to'45'trace'45'slot'45'stable_2294 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'slot'45'stable_2294 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_894
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.just-injℕ
d_just'45'injℕ_2296 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_2296 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.lab-eq
d_lab'45'eq_2298 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_2298 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.label-of?
d_label'45'of'63'_2300 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_2300 ~v0 ~v1 ~v2 = du_label'45'of'63'_2300
du_label'45'of'63'_2300 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_2300
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_122
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.label-of?-sound
d_label'45'of'63''45'sound_2302 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_2302 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame
d_leave'45'frame_2304 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_leave'45'frame_2304 ~v0 ~v1 ~v2 = du_leave'45'frame_2304
du_leave'45'frame_2304 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_leave'45'frame_2304
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_976
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-aux
d_leave'45'frame'45'aux_2306 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_leave'45'frame'45'aux_2306 ~v0 ~v1 ~v2
  = du_leave'45'frame'45'aux_2306
du_leave'45'frame'45'aux_2306 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_leave'45'frame'45'aux_2306
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_964
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-block-size
d_leave'45'frame'45'block'45'size_2308 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_2308 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_2310 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_2310 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_2312 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_2312 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_2314 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_2314 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_2316 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_2316 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_2318 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_2318 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_2320 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_2320 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.load-indirect-suc-twf
d_load'45'indirect'45'suc'45'twf_2322 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'twf_2322 ~v0 ~v1 ~v2
  = du_load'45'indirect'45'suc'45'twf_2322
du_load'45'indirect'45'suc'45'twf_2322 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'twf_2322 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'suc'45'twf_7934
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.load-indirect-twf
d_load'45'indirect'45'twf_2324 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'twf_2324 ~v0 ~v1 ~v2
  = du_load'45'indirect'45'twf_2324
du_load'45'indirect'45'twf_2324 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'twf_2324 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'twf_7916
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.log-abstract
d_log'45'abstract_2326 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'abstract_2326 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.log-of
d_log'45'of_2328 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'of_2328 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.log-pure
d_log'45'pure_2330 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'pure_2330 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.log-silent
d_log'45'silent_2332 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'silent_2332 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.log-step
d_log'45'step_2334 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'step_2334 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.prim-sv
d_prim'45'sv_2340 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_2340 ~v0 ~v1 ~v2 = du_prim'45'sv_2340
du_prim'45'sv_2340 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_2340 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_548
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_2342 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_2342 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'aux_2342 v2
du_pure'45'sigop'45'out'45'aux_2342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'aux_2342 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_3014
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_2344 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_2344 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'val_2344 v2
du_pure'45'sigop'45'out'45'val_2344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_2344 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'val_2990
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.pure-sigop-output
d_pure'45'sigop'45'output_2346 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_2346 ~v0 ~v1 v2
  = du_pure'45'sigop'45'output_2346 v2
du_pure'45'sigop'45'output_2346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'output_2346 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_2984
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readLoc
d_readLoc_2362 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_2362 ~v0 ~v1 ~v2 = du_readLoc_2362
du_readLoc_2362 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_2362
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_2364 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_2364 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readReg-typed
d_readReg'45'typed_2366 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_2366 ~v0 ~v1 ~v2 = du_readReg'45'typed_2366
du_readReg'45'typed_2366 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_2366
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2744
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readTyped
d_readTyped_2368 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe AgdaAny
d_readTyped_2368 ~v0 ~v1 ~v2 = du_readTyped_2368
du_readTyped_2368 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe AgdaAny
du_readTyped_2368
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2800
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readTyped-adequate
d_readTyped'45'adequate_2370 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'adequate_2370 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readable-base
d_readable'45'base_2372 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850
d_readable'45'base_2372 ~v0 ~v1 ~v2 = du_readable'45'base_2372
du_readable'45'base_2372 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850
du_readable'45'base_2372
  = coe
      MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'45'base_880
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readable?
d_readable'63'_2374 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850
d_readable'63'_2374 ~v0 ~v1 ~v2 = du_readable'63'_2374
du_readable'63'_2374 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_850
du_readable'63'_2374
  = coe
      MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'63'_892
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.reg-write-readLoc
d_reg'45'write'45'readLoc_2378 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_120 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'write'45'readLoc_2378 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.reloc-fetch
d_reloc'45'fetch_2380 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'fetch_2380 ~v0 ~v1 v2 = du_reloc'45'fetch_2380 v2
du_reloc'45'fetch_2380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'fetch_2380 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'fetch_3782 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.reloc-step
d_reloc'45'step_2382 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'step_2382 ~v0 ~v1 v2 = du_reloc'45'step_2382 v2
du_reloc'45'step_2382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'step_2382 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'step_3760 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.resultAt
d_resultAt_2388 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_resultAt_2388 ~v0 ~v1 v2 = du_resultAt_2388 v2
du_resultAt_2388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
du_resultAt_2388 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_resultAt_1176
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.retVal
d_retVal_2390 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> AgdaAny -> AgdaAny
d_retVal_2390 ~v0 ~v1 v2 = du_retVal_2390 v2
du_retVal_2390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> AgdaAny -> AgdaAny
du_retVal_2390 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_retVal_1224
      (coe v0) v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.runAt
d_runAt_2392 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runAt_2392 ~v0 ~v1 v2 = du_runAt_2392 v2
du_runAt_2392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runAt_2392 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_runAt_1160
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.runAt-≡
d_runAt'45''8801'_2394 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_runAt'45''8801'_2394 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shift
d_shift_2396 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_shift_2396 ~v0 ~v1 ~v2 = du_shift_2396
du_shift_2396 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_shift_2396
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shift_3428
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shift-loc
d_shift'45'loc_2398 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_2398 ~v0 ~v1 v2 = du_shift'45'loc_2398 v2
du_shift'45'loc_2398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_2398 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shift'45'loc_4356 (coe v0) v1
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-branch
d_shifted'45'branch_2400 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Bool ->
  Bool ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'branch_2400 ~v0 ~v1 ~v2 = du_shifted'45'branch_2400
du_shifted'45'branch_2400 ::
  Integer ->
  Bool ->
  Bool ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'branch_2400 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'branch_1854 v1 v4
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-call-at
d_shifted'45'call'45'at_2402 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'at_2402 ~v0 ~v1 ~v2
  = du_shifted'45'call'45'at_2402
du_shifted'45'call'45'at_2402 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'at_2402 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'at_1992 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-call-closure
d_shifted'45'call'45'closure_2404 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'closure_2404 ~v0 ~v1 v2
  = du_shifted'45'call'45'closure_2404 v2
du_shifted'45'call'45'closure_2404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'closure_2404 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'closure_2208
      (coe v0) v3 v4 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-call-code
d_shifted'45'call'45'code_2406 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'code_2406 ~v0 ~v1 v2
  = du_shifted'45'call'45'code_2406 v2
du_shifted'45'call'45'code_2406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'code_2406 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'code_2040
      (coe v0) v2 v4 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-call-sv
d_shifted'45'call'45'sv_2408 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'sv_2408 ~v0 ~v1 v2
  = du_shifted'45'call'45'sv_2408 v2
du_shifted'45'call'45'sv_2408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'sv_2408 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'sv_2122
      (coe v0) v2 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-eq
d_shifted'45'eq_2410 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shifted'45'eq_2410 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-frame
d_shifted'45'frame_2412 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'frame_2412 ~v0 ~v1 ~v2 = du_shifted'45'frame_2412
du_shifted'45'frame_2412 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'frame_2412 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'frame_1892 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-halt
d_shifted'45'halt_2414 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'halt_2414 ~v0 ~v1 ~v2 = du_shifted'45'halt_2414
du_shifted'45'halt_2414 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'halt_2414 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'halt_1958 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-instr
d_shifted'45'instr_2416 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'instr_2416 ~v0 ~v1 v2 = du_shifted'45'instr_2416 v2
du_shifted'45'instr_2416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'instr_2416 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'instr_2248
      (coe v0) v2 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-jump
d_shifted'45'jump_2418 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'jump_2418 ~v0 ~v1 ~v2 = du_shifted'45'jump_2418
du_shifted'45'jump_2418 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'jump_2418 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'jump_1796 v2 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-label
d_shifted'45'label_2420 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'label_2420 ~v0 ~v1 ~v2 = du_shifted'45'label_2420
du_shifted'45'label_2420 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'label_2420 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'label_1626 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-leave
d_shifted'45'leave_2422 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'leave_2422 ~v0 ~v1 ~v2 = du_shifted'45'leave_2422
du_shifted'45'leave_2422 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'leave_2422 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'leave_1652 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-ret
d_shifted'45'ret_2424 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret_2424 ~v0 ~v1 ~v2 = du_shifted'45'ret_2424
du_shifted'45'ret_2424 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret_2424 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret_1772 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-ret-aux
d_shifted'45'ret'45'aux_2426 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret'45'aux_2426 ~v0 ~v1 ~v2
  = du_shifted'45'ret'45'aux_2426
du_shifted'45'ret'45'aux_2426 ::
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret'45'aux_2426 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret'45'aux_1720 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-save-closure
d_shifted'45'save'45'closure_2428 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'save'45'closure_2428 ~v0 ~v1 ~v2
  = du_shifted'45'save'45'closure_2428
du_shifted'45'save'45'closure_2428 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'save'45'closure_2428 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'save'45'closure_1930
      v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-shift
d_shifted'45'shift_2430 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'shift_2430 ~v0 ~v1 ~v2 = du_shifted'45'shift_2430
du_shifted'45'shift_2430 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'shift_2430 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'shift_3442
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-straight
d_shifted'45'straight_2432 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'straight_2432 ~v0 ~v1 ~v2
  = du_shifted'45'straight_2432
du_shifted'45'straight_2432 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'straight_2432 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'straight_1590 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-thunk
d_shifted'45'thunk_2434 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'thunk_2434 ~v0 ~v1 ~v2 = du_shifted'45'thunk_2434
du_shifted'45'thunk_2434 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'thunk_2434 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'thunk_1682 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.step-at
d_step'45'at_2436 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_step'45'at_2436 ~v0 ~v1 ~v2 = du_step'45'at_2436
du_step'45'at_2436 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_step'45'at_2436 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366 v4
      v6 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.step-dispatch
d_step'45'dispatch_2438 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_step'45'dispatch_2438 ~v0 ~v1 v2 = du_step'45'dispatch_2438 v2
du_step'45'dispatch_2438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_step'45'dispatch_2438 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_step'45'dispatch_3690 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.stopsAt
d_stopsAt_2440 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> Bool
d_stopsAt_2440 ~v0 ~v1 v2 = du_stopsAt_2440 v2
du_stopsAt_2440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> Bool
du_stopsAt_2440 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_stopsAt_1184
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_2442 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_2442 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_2444 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_2444 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.sv-is-zero
d_sv'45'is'45'zero_2446 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_2446 ~v0 ~v1 ~v2 = du_sv'45'is'45'zero_2446
du_sv'45'is'45'zero_2446 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_2446
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.tag-zf
d_tag'45'zf_2448 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_2448 ~v0 ~v1 ~v2 = du_tag'45'zf_2448
du_tag'45'zf_2448 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_2448
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.thunk-of?
d_thunk'45'of'63'_2450 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_2450 ~v0 ~v1 ~v2 = du_thunk'45'of'63'_2450
du_thunk'45'of'63'_2450 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_2450
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63'_176
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.thunk-of?-sound
d_thunk'45'of'63''45'sound_2452 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_2452 ~v0 ~v1 ~v2
  = du_thunk'45'of'63''45'sound_2452
du_thunk'45'of'63''45'sound_2452 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_2452 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63''45'sound_620
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.thunk-part
d_thunk'45'part_2454 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'part_2454 ~v0 ~v1 ~v2 = du_thunk'45'part_2454
du_thunk'45'part_2454 ::
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'part_2454
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'part_172
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.valid-primitive-wf
d_valid'45'primitive'45'wf_2472 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_valid'45'primitive'45'wf_2472 ~v0 ~v1 ~v2
  = du_valid'45'primitive'45'wf_2472
du_valid'45'primitive'45'wf_2472 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
du_valid'45'primitive'45'wf_2472 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'primitive'45'wf_598
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_2478 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'frontier'45'advance_2478 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4408
      (coe v0) (coe v1) (coe v2) v4 v5 v6 v7 v8 v9 v11 v12 v13
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_2480 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'mem'45'preserved_2480 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                      v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5160
      (coe v0) (coe v1) (coe v2) v4 v5 v6 v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_2482 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_validityWF'45'with'45'bf'45'transfer_2482 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'with'45'bf'45'transfer_4824
      (coe v0) (coe v1) (coe v2) v4 v5 v6 v7 v8 v9 v10 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.vr-mem-pres
d_vr'45'mem'45'pres_2484 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vr'45'mem'45'pres_2484 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ιᶠ
d_ι'7584'_2486 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
d_ι'7584'_2486 ~v0 ~v1 v2 = du_ι'7584'_2486 v2
du_ι'7584'_2486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
du_ι'7584'_2486 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_ι'7584'_1150
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.μ-layer-iso
d_μ'45'layer'45'iso_2488 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_μ'45'layer'45'iso_2488 ~v0 ~v1 ~v2 = du_μ'45'layer'45'iso_2488
du_μ'45'layer'45'iso_2488 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
du_μ'45'layer'45'iso_2488 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_μ'45'layer'45'iso_1948
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.≡ᵇ-true
d_'8801''7495''45'true_2490 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_2490 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlockRuns.closures
d_closures_2502 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closures_2502 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_closures_2592
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlockRuns.coalgs
d_coalgs_2504 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coalgs_2504 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_2594
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlockRuns.functions
d_functions_2506 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_functions_2506 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_functions_2596
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.bf-mono
d_bf'45'mono_2516 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'mono_2516 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_2474
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.cont-alloc
d_cont'45'alloc_2518 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_2518 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_2434
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.events
d_events_2520 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_2520 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.frame-pres
d_frame'45'pres_2522 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_2522 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.live
d_live_2524 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_2524 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.log
d_log_2526 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_2526 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.mem-pres
d_mem'45'pres_2528 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_2528 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.no-link
d_no'45'link_2530 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_2530 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.no-ret
d_no'45'ret_2532 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_2532 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.out-mode
d_out'45'mode_2534 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_2534 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_2432
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.place
d_place_2536 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_2536 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_2450
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.returned
d_returned_2538 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_2538 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.run
d_run_2540 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_2540 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_2436
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.settle
d_settle_2542 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_2542 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_2430
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.steps
d_steps_2544 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  Integer
d_steps_2544 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2428
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.stops
d_stops_2546 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stops_2546 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_stops_2442
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.falloc
d_falloc_2582 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_2582 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.fclosure
d_fclosure_2584 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_2584 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.flink
d_flink_2586 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_2586 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.floc
d_floc_2588 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_floc_2588 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.fpc
d_fpc_2590 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_2590 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.fret
d_fret_2592 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_2592 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.MachineRefinesObsF.traces-agree
d_traces'45'agree_2628 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_2628 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.MachineRefinesObsF.value-realized
d_value'45'realized_2630 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102
d_value'45'realized_2630 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_2316
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.at-end
d_at'45'end_2692 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_2692 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.bf-mono
d_bf'45'mono_2694 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'mono_2694 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_2214
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.cont-alloc
d_cont'45'alloc_2696 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_2696 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_2178
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.frame-pres
d_frame'45'pres_2698 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_2698 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.heap-pres
d_heap'45'pres_2700 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_2700 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.live
d_live_2702 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_2702 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.log
d_log_2704 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_2704 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.no-link
d_no'45'link_2706 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_2706 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.no-ret
d_no'45'ret_2708 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_2708 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.out-mode
d_out'45'mode_2710 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_2710 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_2176
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.place
d_place_2712 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_2712 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_2196
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.run
d_run_2714 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_2714 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_2180
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.settle
d_settle_2716 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_2716 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_2174
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.stack-pres
d_stack'45'pres_2718 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_2718 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.steps
d_steps_2720 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  Integer
d_steps_2720 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2172
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.stops
d_stops_2722 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stops_2722 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_stops_2186
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_2726 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.SMPrimitives.instr-writes-slot
d_instr'45'writes'45'slot_2728 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe Integer
d_instr'45'writes'45'slot_2728 ~v0 ~v1 ~v2
  = du_instr'45'writes'45'slot_2728
du_instr'45'writes'45'slot_2728 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Maybe Integer
du_instr'45'writes'45'slot_2728
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_instr'45'writes'45'slot_692
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.flat-store-floc
d_flat'45'store'45'floc_2814 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'store'45'floc_2814 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.flat-store-falloc
d_flat'45'store'45'falloc_2828 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'store'45'falloc_2828 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.flat-store-fpc
d_flat'45'store'45'fpc_2842 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'store'45'fpc_2842 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-preserves-input
d_store'45'ind'45'preserves'45'input_2856 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'preserves'45'input_2856 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.load-ind-suc-preserves-input
d_load'45'ind'45'suc'45'preserves'45'input_2888 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'ind'45'suc'45'preserves'45'input_2888 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.load-ind-preserves-input
d_load'45'ind'45'preserves'45'input_2942 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'ind'45'preserves'45'input_2942 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.load-slot-preserves-input
d_load'45'slot'45'preserves'45'input_2996 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'slot'45'preserves'45'input_2996 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-preserves-slot
d_store'45'ind'45'preserves'45'slot_3032 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'preserves'45'slot_3032 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.writeLoc-heap-eq
d_writeLoc'45'heap'45'eq_3068 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heap'45'eq_3068 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.heap-read-toheap
d_heap'45'read'45'toheap_3096 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'read'45'toheap_3096 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.heap-read-same
d_heap'45'read'45'same_3128 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'read'45'same_3128 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-result
d_store'45'ind'45'result_3144 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'result_3144 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-suc-result
d_store'45'ind'45'suc'45'result_3172 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'suc'45'result_3172 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.load-slot-result
d_load'45'slot'45'result_3202 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'slot'45'result_3202 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.sucHL-≢
d_sucHL'45''8802'_3230 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sucHL'45''8802'_3230 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.heap-untouched
d_heap'45'untouched_3244 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'untouched_3244 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-suc-preserves-heap
d_store'45'ind'45'suc'45'preserves'45'heap_3266 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'suc'45'preserves'45'heap_3266 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-suc-preserves-slot
d_store'45'ind'45'suc'45'preserves'45'slot_3306 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'suc'45'preserves'45'slot_3306 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.mem-untouched
d_mem'45'untouched_3344 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'untouched_3344 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-slot-preserves-before
d_store'45'slot'45'preserves'45'before_3382 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'preserves'45'before_3382 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.sucHL-ref
d_sucHL'45'ref_3442 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucHL'45'ref_3442 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.fresh-heap-≢
d_fresh'45'heap'45''8802'_3454 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'heap'45''8802'_3454 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-preserves-before
d_store'45'ind'45'preserves'45'before_3476 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'preserves'45'before_3476 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-suc-preserves-before
d_store'45'ind'45'suc'45'preserves'45'before_3556 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'suc'45'preserves'45'before_3556 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineSteps.u2
d_u2_3618 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u2_3618 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 = du_u2_3618 v2 v3 v6
du_u2_3618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u2_3618 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
         (coe v1))
      (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineSteps.u3
d_u3_3620 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u3_3620 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 = du_u3_3620 v2 v3 v6
du_u3_3620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u3_3620 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2314
         (coe (2 :: Integer)))
      (coe du_u2_3618 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineSteps.u4
d_u4_3622 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u4_3622 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 = du_u4_3622 v2 v3 v6
du_u4_3622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u4_3622 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_u3_3620 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineSteps.u5
d_u5_3624 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u5_3624 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 = du_u5_3624 v2 v3 v6
du_u5_3624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u5_3624 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
      (coe du_u4_3622 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineSteps.u6
d_u6_3626 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u6_3626 ~v0 ~v1 v2 v3 v4 ~v5 v6 = du_u6_3626 v2 v3 v4 v6
du_u6_3626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u6_3626 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0) (coe v2) (coe du_u5_3624 (coe v0) (coe v1) (coe v3))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineSteps.u7
d_u7_3628 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u7_3628 ~v0 ~v1 v2 v3 v4 ~v5 v6 = du_u7_3628 v2 v3 v4 v6
du_u7_3628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u7_3628 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2266)
      (coe du_u6_3626 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineSteps.u8
d_u8_3630 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u8_3630 ~v0 ~v1 v2 v3 v4 v5 v6 = du_u8_3630 v2 v3 v4 v5 v6
du_u8_3630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u8_3630 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0) (coe v3)
      (coe du_u7_3628 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineSteps.u9
d_u9_3632 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u9_3632 ~v0 ~v1 v2 v3 v4 v5 v6 = du_u9_3632 v2 v3 v4 v5 v6
du_u9_3632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u9_3632 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2268)
      (coe du_u8_3630 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineSteps.u10
d_u10_3634 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u10_3634 ~v0 ~v1 v2 v3 v4 v5 v6 = du_u10_3634 v2 v3 v4 v5 v6
du_u10_3634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u10_3634 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_u9_3632 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres._.u10
d_u10_3656 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u10_3656 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u10_3656 v2 v3 v4 v5 v6
du_u10_3656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u10_3656 v0 v1 v2 v3 v4
  = coe du_u10_3634 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres._.u2
d_u2_3658 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u2_3658 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u2_3658 v2 v3 v6
du_u2_3658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u2_3658 v0 v1 v2 = coe du_u2_3618 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres._.u3
d_u3_3660 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u3_3660 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u3_3660 v2 v3 v6
du_u3_3660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u3_3660 v0 v1 v2 = coe du_u3_3620 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres._.u4
d_u4_3662 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u4_3662 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u4_3662 v2 v3 v6
du_u4_3662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u4_3662 v0 v1 v2 = coe du_u4_3622 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres._.u5
d_u5_3664 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u5_3664 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u5_3664 v2 v3 v6
du_u5_3664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u5_3664 v0 v1 v2 = coe du_u5_3624 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres._.u6
d_u6_3666 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u6_3666 ~v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u6_3666 v2 v3 v4 v6
du_u6_3666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u6_3666 v0 v1 v2 v3
  = coe du_u6_3626 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres._.u7
d_u7_3668 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u7_3668 ~v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u7_3668 v2 v3 v4 v6
du_u7_3668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u7_3668 v0 v1 v2 v3
  = coe du_u7_3628 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres._.u8
d_u8_3670 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u8_3670 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u8_3670 v2 v3 v4 v5 v6
du_u8_3670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u8_3670 v0 v1 v2 v3 v4
  = coe du_u8_3630 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres._.u9
d_u9_3672 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u9_3672 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u9_3672 v2 v3 v4 v5 v6
du_u9_3672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u9_3672 v0 v1 v2 v3 v4
  = coe du_u9_3632 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.hl
d_hl_3674 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
d_hl_3674 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_hl_3674 v2 v3 v6
du_hl_3674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
du_hl_3674 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_48
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
               (coe du_u2_3618 (coe v0) (coe v1) (coe v2)))))
      (coe (0 :: Integer))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.heapref-u2
d_heapref'45'u2_3676 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'u2_3676 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.fresh
d_fresh_3678 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_3678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_fresh_3678 v8
du_fresh_3678 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_3678 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.cf-u3
d_cf'45'u3_3680 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'u3_3680 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.mem-pres-from
d_mem'45'pres'45'from_3684 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'from_3684 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t0
d_t0_3732 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t0_3732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13
          ~v14
  = du_t0_3732 v8 v9 v10 v11
du_t0_3732 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t0_3732 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_entry'45'flat_1986
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t1
d_t1_3734 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t1_3734 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13
          ~v14
  = du_t1_3734 v2 v3 v8 v9 v10 v11
du_t1_3734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t1_3734 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0) (coe v1)
      (coe du_t0_3732 (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.cf-u3
d_cf'45'u3_3738 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'u3_3738 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.fresh
d_fresh_3740 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_3740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
             ~v13 ~v14
  = du_fresh_3740 v10
du_fresh_3740 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_3740 v0 = coe du_fresh_3678 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.heapref-u2
d_heapref'45'u2_3742 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'u2_3742 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.hl
d_hl_3744 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
d_hl_3744 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_hl_3744 v2 v3 v4 v8 v9 v10 v11
du_hl_3744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
du_hl_3744 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_hl_3674 (coe v0) (coe v2)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.mem-pres-from
d_mem'45'pres'45'from_3746 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'from_3746 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.u10
d_u10_3748 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u10_3748 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_u10_3748 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_u10_3748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u10_3748 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = let v9
          = coe
              du_t1_3734 (coe v0) (coe v1) (coe v5) (coe v6) (coe v7) (coe v8) in
    coe (coe du_u10_3634 (coe v0) (coe v2) (coe v3) (coe v4) (coe v9))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.u2
d_u2_3750 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u2_3750 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_u2_3750 v2 v3 v4 v8 v9 v10 v11
du_u2_3750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u2_3750 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6) in
    coe (coe du_u2_3618 (coe v0) (coe v2) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.u3
d_u3_3752 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u3_3752 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_u3_3752 v2 v3 v4 v8 v9 v10 v11
du_u3_3752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u3_3752 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6) in
    coe (coe du_u3_3620 (coe v0) (coe v2) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.u4
d_u4_3754 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u4_3754 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_u4_3754 v2 v3 v4 v8 v9 v10 v11
du_u4_3754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u4_3754 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6) in
    coe (coe du_u4_3622 (coe v0) (coe v2) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.u5
d_u5_3756 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u5_3756 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_u5_3756 v2 v3 v4 v8 v9 v10 v11
du_u5_3756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u5_3756 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6) in
    coe (coe du_u5_3624 (coe v0) (coe v2) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.u6
d_u6_3758 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u6_3758 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_u6_3758 v2 v3 v4 v5 v8 v9 v10 v11
du_u6_3758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u6_3758 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              du_t1_3734 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6) (coe v7) in
    coe (coe du_u6_3626 (coe v0) (coe v2) (coe v3) (coe v8))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.u7
d_u7_3760 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u7_3760 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_u7_3760 v2 v3 v4 v5 v8 v9 v10 v11
du_u7_3760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u7_3760 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              du_t1_3734 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6) (coe v7) in
    coe (coe du_u7_3628 (coe v0) (coe v2) (coe v3) (coe v8))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.u8
d_u8_3762 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u8_3762 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_u8_3762 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_u8_3762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u8_3762 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = let v9
          = coe
              du_t1_3734 (coe v0) (coe v1) (coe v5) (coe v6) (coe v7) (coe v8) in
    coe (coe du_u8_3630 (coe v0) (coe v2) (coe v3) (coe v4) (coe v9))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.NSP.u9
d_u9_3764 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u9_3764 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_u9_3764 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_u9_3764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u9_3764 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = let v9
          = coe
              du_t1_3734 (coe v0) (coe v1) (coe v5) (coe v6) (coe v7) (coe v8) in
    coe (coe du_u9_3632 (coe v0) (coe v2) (coe v3) (coe v4) (coe v9))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t2
d_t2_3766 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t2_3766 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_t2_3766 v2 v3 v4 v8 v9 v10 v11
du_t2_3766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t2_3766 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_u2_3618 (coe v0) (coe v2)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t3
d_t3_3768 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t3_3768 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_t3_3768 v2 v3 v4 v8 v9 v10 v11
du_t3_3768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t3_3768 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_u3_3620 (coe v0) (coe v2)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t4
d_t4_3770 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t4_3770 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_t4_3770 v2 v3 v4 v8 v9 v10 v11
du_t4_3770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t4_3770 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_u4_3622 (coe v0) (coe v2)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t5
d_t5_3772 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t5_3772 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_t5_3772 v2 v3 v4 v8 v9 v10 v11
du_t5_3772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t5_3772 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_u5_3624 (coe v0) (coe v2)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t6
d_t6_3774 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t6_3774 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_t6_3774 v2 v3 v4 v5 v8 v9 v10 v11
du_t6_3774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t6_3774 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_u6_3626 (coe v0) (coe v2) (coe v3)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t7
d_t7_3776 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t7_3776 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_t7_3776 v2 v3 v4 v5 v8 v9 v10 v11
du_t7_3776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t7_3776 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_u7_3628 (coe v0) (coe v2) (coe v3)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t8
d_t8_3778 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t8_3778 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_t8_3778 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_t8_3778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t8_3778 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_u8_3630 (coe v0) (coe v2) (coe v3) (coe v4)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v5) (coe v6) (coe v7) (coe v8))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t9
d_t9_3780 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t9_3780 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_t9_3780 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_t9_3780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t9_3780 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_u9_3632 (coe v0) (coe v2) (coe v3) (coe v4)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v5) (coe v6) (coe v7) (coe v8))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.t10
d_t10_3782 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t10_3782 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_t10_3782 v2 v3 v4 v5 v6 v8 v9 v10 v11
du_t10_3782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t10_3782 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_u10_3634 (coe v0) (coe v2) (coe v3) (coe v4)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v5) (coe v6) (coe v7) (coe v8))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.hl
d_hl_3784 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
d_hl_3784 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
  = du_hl_3784 v2 v3 v4 v8 v9 v10 v11
du_hl_3784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
du_hl_3784 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_hl_3674 (coe v0) (coe v2)
      (coe
         du_t1_3734 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.heapref-t2
d_heapref'45't2_3786 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45't2_3786 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.fresh
d_fresh_3788 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_3788 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
             ~v13 ~v14
  = du_fresh_3788 v10
du_fresh_3788 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_3788 v0 = coe du_fresh_3678 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.cf-t3
d_cf'45't3_3790 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45't3_3790 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPresAt.mem-pres
d_mem'45'pres_3794 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_3794 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.cf-t3
d_cf'45't3_3834 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45't3_3834 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.fresh
d_fresh_3836 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_3836 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_fresh_3836 v9
du_fresh_3836 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_3836 v0 = coe du_fresh_3788 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.heapref-t2
d_heapref'45't2_3838 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45't2_3838 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.hl
d_hl_3840 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
d_hl_3840 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_hl_3840 v2 v3 v7 v8 v9 v10
du_hl_3840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
du_hl_3840 v0 v1 v2 v3 v4 v5
  = coe
      du_hl_3784 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.mem-pres
d_mem'45'pres_3842 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_3842 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t0
d_t0_3844 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t0_3844 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_t0_3844 v7 v8 v9 v10
du_t0_3844 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t0_3844 v0 v1 v2 v3
  = coe du_t0_3732 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t1
d_t1_3846 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t1_3846 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_t1_3846 v2 v7 v8 v9 v10
du_t1_3846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t1_3846 v0 v1 v2 v3 v4
  = coe
      du_t1_3734 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t10
d_t10_3848 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t10_3848 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_t10_3848 v2 v3 v4 v5 v7 v8 v9 v10
du_t10_3848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t10_3848 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_t10_3782 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t2
d_t2_3850 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t2_3850 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_t2_3850 v2 v3 v7 v8 v9 v10
du_t2_3850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t2_3850 v0 v1 v2 v3 v4 v5
  = coe
      du_t2_3766 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t3
d_t3_3852 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t3_3852 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_t3_3852 v2 v3 v7 v8 v9 v10
du_t3_3852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t3_3852 v0 v1 v2 v3 v4 v5
  = coe
      du_t3_3768 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t4
d_t4_3854 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t4_3854 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_t4_3854 v2 v3 v7 v8 v9 v10
du_t4_3854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t4_3854 v0 v1 v2 v3 v4 v5
  = coe
      du_t4_3770 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t5
d_t5_3856 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t5_3856 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_t5_3856 v2 v3 v7 v8 v9 v10
du_t5_3856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t5_3856 v0 v1 v2 v3 v4 v5
  = coe
      du_t5_3772 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t6
d_t6_3858 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t6_3858 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10
  = du_t6_3858 v2 v3 v4 v7 v8 v9 v10
du_t6_3858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t6_3858 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_t6_3774 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t7
d_t7_3860 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t7_3860 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10
  = du_t7_3860 v2 v3 v4 v7 v8 v9 v10
du_t7_3860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t7_3860 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_t7_3776 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t8
d_t8_3862 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t8_3862 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_t8_3862 v2 v3 v4 v5 v7 v8 v9 v10
du_t8_3862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t8_3862 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_t8_3778 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t9
d_t9_3864 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t9_3864 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_t9_3864 v2 v3 v4 v5 v7 v8 v9 v10
du_t9_3864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t9_3864 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_t9_3780 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.cf-u3
d_cf'45'u3_3868 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'u3_3868 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.fresh
d_fresh_3870 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_3870 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_fresh_3870 v9
du_fresh_3870 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_3870 v0 = coe du_fresh_3678 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.heapref-u2
d_heapref'45'u2_3872 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'u2_3872 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.hl
d_hl_3874 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
d_hl_3874 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_hl_3874 v2 v3 v7 v8 v9 v10
du_hl_3874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
du_hl_3874 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (coe
         du_hl_3674 (coe v0) (coe v1)
         (coe
            du_t1_3734 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4) (coe v5)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.mem-pres-from
d_mem'45'pres'45'from_3876 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_762 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'from_3876 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u10
d_u10_3878 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u10_3878 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_u10_3878 v2 v3 v4 v5 v7 v8 v9 v10
du_u10_3878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u10_3878 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (let v9
             = coe
                 du_t1_3734 (coe v0) (coe v8) (coe v4) (coe v5) (coe v6) (coe v7) in
       coe (coe du_u10_3634 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u2
d_u2_3880 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u2_3880 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_u2_3880 v2 v3 v7 v8 v9 v10
du_u2_3880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u2_3880 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (let v7
             = coe
                 du_t1_3734 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4) (coe v5) in
       coe (coe du_u2_3618 (coe v0) (coe v1) (coe v7)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u3
d_u3_3882 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u3_3882 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_u3_3882 v2 v3 v7 v8 v9 v10
du_u3_3882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u3_3882 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (let v7
             = coe
                 du_t1_3734 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4) (coe v5) in
       coe (coe du_u3_3620 (coe v0) (coe v1) (coe v7)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u4
d_u4_3884 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u4_3884 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_u4_3884 v2 v3 v7 v8 v9 v10
du_u4_3884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u4_3884 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (let v7
             = coe
                 du_t1_3734 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4) (coe v5) in
       coe (coe du_u4_3622 (coe v0) (coe v1) (coe v7)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u5
d_u5_3886 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u5_3886 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_u5_3886 v2 v3 v7 v8 v9 v10
du_u5_3886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u5_3886 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (let v7
             = coe
                 du_t1_3734 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4) (coe v5) in
       coe (coe du_u5_3624 (coe v0) (coe v1) (coe v7)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u6
d_u6_3888 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u6_3888 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10
  = du_u6_3888 v2 v3 v4 v7 v8 v9 v10
du_u6_3888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u6_3888 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (let v8
             = coe
                 du_t1_3734 (coe v0) (coe v7) (coe v3) (coe v4) (coe v5) (coe v6) in
       coe (coe du_u6_3626 (coe v0) (coe v1) (coe v2) (coe v8)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u7
d_u7_3890 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u7_3890 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10
  = du_u7_3890 v2 v3 v4 v7 v8 v9 v10
du_u7_3890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u7_3890 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (let v8
             = coe
                 du_t1_3734 (coe v0) (coe v7) (coe v3) (coe v4) (coe v5) (coe v6) in
       coe (coe du_u7_3628 (coe v0) (coe v1) (coe v2) (coe v8)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u8
d_u8_3892 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u8_3892 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_u8_3892 v2 v3 v4 v5 v7 v8 v9 v10
du_u8_3892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u8_3892 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (let v9
             = coe
                 du_t1_3734 (coe v0) (coe v8) (coe v4) (coe v5) (coe v6) (coe v7) in
       coe (coe du_u8_3630 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u9
d_u9_3894 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u9_3894 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_u9_3894 v2 v3 v4 v5 v7 v8 v9 v10
du_u9_3894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u9_3894 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254 in
    coe
      (let v9
             = coe
                 du_t1_3734 (coe v0) (coe v8) (coe v4) (coe v5) (coe v6) (coe v7) in
       coe (coe du_u9_3632 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.arg-stash
d_arg'45'stash_3910 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_arg'45'stash_3910 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_arg'45'stash_3910 v3
du_arg'45'stash_3910 :: Integer -> Integer
du_arg'45'stash_3910 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.env-stash
d_env'45'stash_3912 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_env'45'stash_3912 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_env'45'stash_3912 v3
du_env'45'stash_3912 :: Integer -> Integer
du_env'45'stash_3912 v0 = coe addInt (coe (1 :: Integer)) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.pair-stash
d_pair'45'stash_3914 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_pair'45'stash_3914 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_pair'45'stash_3914 v3
du_pair'45'stash_3914 :: Integer -> Integer
du_pair'45'stash_3914 v0 = coe addInt (coe (2 :: Integer)) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a0
d_a0_3916 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a0_3916 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_a0_3916 v5 v6 v7 v8
du_a0_3916 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a0_3916 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_entry'45'flat_1986
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a1
d_a1_3918 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a1_3918 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8
  = du_a1_3918 v2 v5 v6 v7 v8
du_a1_3918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a1_3918 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2260)
      (coe du_a0_3916 (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a2
d_a2_3920 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a2_3920 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a2_3920 v2 v3 v5 v6 v7 v8
du_a2_3920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a2_3920 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
         (coe v1))
      (coe du_a1_3918 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a3
d_a3_3922 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a3_3922 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a3_3922 v2 v3 v5 v6 v7 v8
du_a3_3922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a3_3922 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258)
      (coe
         du_a2_3920 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a4
d_a4_3924 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a4_3924 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a4_3924 v2 v3 v5 v6 v7 v8
du_a4_3924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a4_3924 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
      (coe
         du_a3_3922 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a5
d_a5_3926 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a5_3926 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a5_3926 v2 v3 v5 v6 v7 v8
du_a5_3926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a5_3926 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1498
      (coe
         du_a4_3924 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a6
d_a6_3928 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a6_3928 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a6_3928 v2 v3 v5 v6 v7 v8
du_a6_3928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a6_3928 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258)
      (coe
         du_a5_3926 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a7
d_a7_3930 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a7_3930 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a7_3930 v2 v3 v5 v6 v7 v8
du_a7_3930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a7_3930 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
         (coe du_env'45'stash_3912 (coe v1)))
      (coe
         du_a6_3928 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a8
d_a8_3932 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a8_3932 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a8_3932 v2 v3 v5 v6 v7 v8
du_a8_3932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a8_3932 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2314
         (coe (2 :: Integer)))
      (coe
         du_a7_3930 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a9
d_a9_3934 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a9_3934 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a9_3934 v2 v3 v5 v6 v7 v8
du_a9_3934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a9_3934 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
         (coe du_pair'45'stash_3914 (coe v1)))
      (coe
         du_a8_3932 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a10
d_a10_3936 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a10_3936 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a10_3936 v2 v3 v5 v6 v7 v8
du_a10_3936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a10_3936 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
      (coe
         du_a9_3934 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a11
d_a11_3938 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a11_3938 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a11_3938 v2 v3 v5 v6 v7 v8
du_a11_3938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a11_3938 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
         (coe du_env'45'stash_3912 (coe v1)))
      (coe
         du_a10_3936 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a12
d_a12_3940 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a12_3940 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a12_3940 v2 v3 v5 v6 v7 v8
du_a12_3940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a12_3940 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2266)
      (coe
         du_a11_3938 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a13
d_a13_3942 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a13_3942 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a13_3942 v2 v3 v5 v6 v7 v8
du_a13_3942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a13_3942 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
         (coe v1))
      (coe
         du_a12_3940 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a14
d_a14_3944 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a14_3944 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a14_3944 v2 v3 v5 v6 v7 v8
du_a14_3944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a14_3944 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2268)
      (coe
         du_a13_3942 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a15
d_a15_3946 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a15_3946 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a15_3946 v2 v3 v5 v6 v7 v8
du_a15_3946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a15_3946 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
         (coe du_pair'45'stash_3914 (coe v1)))
      (coe
         du_a14_3944 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a16
d_a16_3948 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a16_3948 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_a16_3948 v2 v3 v5 v6 v7 v8
du_a16_3948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a16_3948 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
      (coe
         du_a15_3946 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.ahl
d_ahl_3950 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
d_ahl_3950 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_ahl_3950 v2 v3 v5 v6 v7 v8
du_ahl_3950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
du_ahl_3950 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_48
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
               (coe
                  du_a7_3930 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v5)))))
      (coe (0 :: Integer))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.heapref-a7
d_heapref'45'a7_3952 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'a7_3952 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.fresh-a
d_fresh'45'a_3954 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh'45'a_3954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_fresh'45'a_3954 v7
du_fresh'45'a_3954 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh'45'a_3954 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a1
d_cf'45'a1_3956 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a1_3956 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a6
d_cf'45'a6_3958 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a6_3958 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a8
d_cf'45'a8_3960 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a8_3960 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a10
d_cf'45'a10_3962 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a10_3962 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a12
d_cf'45'a12_3964 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a12_3964 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a14
d_cf'45'a14_3966 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a14_3966 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.setup-mem-pres
d_setup'45'mem'45'pres_3970 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'mem'45'pres_3970 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.input1-a2
d_input1'45'a2_3986 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'a2_3986 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.pair-cell-a2
d_pair'45'cell'45'a2_4000 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'cell'45'a2_4000 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf1
d_wf1_4034 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf1_4034 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 v11 ~v12
           ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_wf1_4034 v9 v11 v15
du_wf1_4034 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf1_4034 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf3
d_wf3_4036 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf3_4036 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_wf3_4036 v9 v10
du_wf3_4036 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf3_4036 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v1))
            erased))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.input1-a5
d_input1'45'a5_4038 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'a5_4038 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-cell-a5
d_env'45'cell'45'a5_4040 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'cell'45'a5_4040 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf6
d_wf6_4042 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf6_4042 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_wf6_4042 v10 v12
du_wf6_4042 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf6_4042 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh0
d_nh0_4044 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh0_4044 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh1
d_nh1_4046 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh1_4046 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh2
d_nh2_4048 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh2_4048 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh3
d_nh3_4050 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh3_4050 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh4
d_nh4_4052 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh4_4052 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh5
d_nh5_4054 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh5_4054 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh6
d_nh6_4056 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh6_4056 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh7
d_nh7_4058 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh7_4058 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh8
d_nh8_4060 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh8_4060 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh9
d_nh9_4062 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh9_4062 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh10
d_nh10_4064 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh10_4064 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-sv'
d_env'45'sv''_4066 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_env'45'sv''_4066 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12
                   ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_env'45'sv''_4066 v2 v3 v5 v6 v7 v8
du_env'45'sv''_4066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_env'45'sv''_4066 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_144
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_424
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
            (coe
               du_a6_3928 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-a7
d_env'45'a7_4068 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'a7_4068 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-a10
d_env'45'a10_4070 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'a10_4070 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.alloc-out
d_alloc'45'out_4072 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'out_4072 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.input1-a10
d_input1'45'a10_4074 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'a10_4074 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf11
d_wf11_4078 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf11_4078 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_wf11_4078 v2 v3 v5 v6 v7 v8
du_wf11_4078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf11_4078 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_env'45'sv''_4066 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.rdi12'
d_rdi12''_4082 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi12''_4082 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.arg-stashed
d_arg'45'stashed_4084 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_arg'45'stashed_4084 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11
                      ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_arg'45'stashed_4084 v2 v5 v6 v7 v8
du_arg'45'stashed_4084 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_arg'45'stashed_4084 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_144
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_424
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
            (coe du_a1_3918 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.arg-a2
d_arg'45'a2_4086 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'a2_4086 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.arg-a12
d_arg'45'a12_4088 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'a12_4088 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf13
d_wf13_4090 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf13_4090 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_wf13_4090 v2 v5 v6 v7 v8
du_wf13_4090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf13_4090 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_arg'45'stashed_4084 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
      erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.rdi14'
d_rdi14''_4094 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi14''_4094 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.newpair-sv
d_newpair'45'sv_4096 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_newpair'45'sv_4096 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11
                     ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_newpair'45'sv_4096 v2 v3 v5 v6 v7 v8
du_newpair'45'sv_4096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_newpair'45'sv_4096 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_144
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_424
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
            (coe
               du_a8_3932 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.newpair-a9
d_newpair'45'a9_4098 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newpair'45'a9_4098 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.newpair-a14
d_newpair'45'a14_4100 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newpair'45'a14_4100 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf15
d_wf15_4102 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf15_4102 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_wf15_4102 v2 v3 v5 v6 v7 v8
du_wf15_4102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf15_4102 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_newpair'45'sv_4096 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh11
d_nh11_4106 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh11_4106 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh12
d_nh12_4108 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh12_4108 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh13
d_nh13_4110 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh13_4110 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh14
d_nh14_4112 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh14_4112 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh15
d_nh15_4114 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh15_4114 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh16
d_nh16_4116 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh16_4116 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.input1-a16
d_input1'45'a16_4118 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'a16_4118 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-sv'≡
d_env'45'sv'''8801'_4120 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'sv'''8801'_4120 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.arg-stashed≡
d_arg'45'stashed'8801'_4122 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'stashed'8801'_4122 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.envout-a11
d_envout'45'a11_4124 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_envout'45'a11_4124 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.argout-a13
d_argout'45'a13_4126 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_argout'45'a13_4126 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.pair-fst-a16
d_pair'45'fst'45'a16_4128 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'fst'45'a16_4128 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.pair-snd-a16
d_pair'45'snd'45'a16_4130 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'snd'45'a16_4130 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.heapref-a16
d_heapref'45'a16_4132 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'a16_4132 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.before-ahl
d_before'45'ahl_4134 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_before'45'ahl_4134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_before'45'ahl_4134 v7
du_before'45'ahl_4134 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
du_before'45'ahl_4134 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_606
      (MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v0)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.before-ahl-suc
d_before'45'ahl'45'suc_4138 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_before'45'ahl'45'suc_4138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_before'45'ahl'45'suc_4138 v7
du_before'45'ahl'45'suc_4138 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
du_before'45'ahl'45'suc_4138 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_606
      (MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v0)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.cf-a16
d_cf'45'a16_4142 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a16_4142 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nextslot-a16
d_nextslot'45'a16_4144 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nextslot'45'a16_4144 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nextslot-a16-≤
d_nextslot'45'a16'45''8804'_4146 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nextslot'45'a16'45''8804'_4146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
                                 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_nextslot'45'a16'45''8804'_4146 v7
du_nextslot'45'a16'45''8804'_4146 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_nextslot'45'a16'45''8804'_4146 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.heapref-a16-≤
d_heapref'45'a16'45''8804'_4148 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heapref'45'a16'45''8804'_4148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
                                ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_heapref'45'a16'45''8804'_4148 v7
du_heapref'45'a16'45''8804'_4148 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heapref'45'a16'45''8804'_4148 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.bf-advance
d_bf'45'advance_4156 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'advance_4156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22
  = du_bf'45'advance_4156 v7 v22
du_bf'45'advance_4156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
du_bf'45'advance_4156 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_592 v5
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_592
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v5) (coe du_nextslot'45'a16'45''8804'_4146 (coe v0)))
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_602 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_602 v4
             v5 v6 v7
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_606 v3
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_606
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v3) (coe du_heapref'45'a16'45''8804'_4148 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.carry
d_carry_4178 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
d_carry_4178 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
             ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 v23 v24 ~v25 v26
  = du_carry_4178 v0 v1 v2 v3 v5 v6 v7 v8 v22 v23 v24 v26
du_carry_4178 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582
du_carry_4178 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4408
      (coe v0) (coe v1) (coe v2) (coe v6)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
         (coe
            du_a16_3948 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)))
      (coe v8) (coe v9) (coe v10)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
         (coe
            du_a16_3948 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)))
      (coe du_nextslot'45'a16'45''8804'_4146 (coe v6))
      (coe du_heapref'45'a16'45''8804'_4148 (coe v6))
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5160
         (coe v0) (coe v1) (coe v2) (coe v6) (coe v8) (coe v9) (coe v5)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
            (coe
               du_a16_3948 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)))
         (coe v11))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.mem-pres
d_mem'45'pres_4194 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_4194 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.closure-reg
d_closure'45'reg_4202 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closure'45'reg_4202 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.code-cell
d_code'45'cell_4224 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'cell_4224 = erased
