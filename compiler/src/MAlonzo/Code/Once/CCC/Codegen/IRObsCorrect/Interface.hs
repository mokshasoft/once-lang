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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface where

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
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Size
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Codegen.IRObsCorrect.Interface._.Bool.Bool
d_Bool_11 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Unit.⊤
d_'8868'_13 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Sigma.Σ
d_Σ_15 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.budget-of
d_budget'45'of_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_16 ~v0 ~v1 = du_budget'45'of_16
du_budget'45'of_16 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_budget'45'of_16
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_budget'45'of_78
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractReg.AbstractReg
d_AbstractReg_17 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.fits-erase
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
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InitLast.InitLast
d_InitLast_19 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.frontier-mono
d_frontier'45'mono_20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_20 v0 ~v1 = du_frontier'45'mono_20 v0
du_frontier'45'mono_20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_frontier'45'mono_20 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotBudget.d_frontier'45'mono_150
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ir-to-trace
d_ir'45'to'45'trace_22 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_ir'45'to'45'trace_22 v0 ~v1 = du_ir'45'to'45'trace_22 v0
du_ir'45'to'45'trace_22 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_ir'45'to'45'trace_22 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_806
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ir-to-trace'
d_ir'45'to'45'trace''_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_24 v0 ~v1 = du_ir'45'to'45'trace''_24 v0
du_ir'45'to'45'trace''_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ir'45'to'45'trace''_24 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.validAtWF-set-halted
d_validAtWF'45'set'45'halted_26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validAtWF'45'set'45'halted_26 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ValidAtWFHalted.du_validAtWF'45'set'45'halted_1328
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v10
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.AllI→All
d_AllI'8594'All_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_AllI'8594'All_30 ~v0 ~v1 = du_AllI'8594'All_30
du_AllI'8594'All_30 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_AllI'8594'All_30 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_AllI'8594'All_160
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.All→AllI
d_All'8594'AllI_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_All'8594'AllI_32 ~v0 ~v1 = du_All'8594'AllI_32
du_All'8594'AllI_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_All'8594'AllI_32 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_All'8594'AllI_106
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.BlockStable
d_BlockStable_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockStable_34 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.all-stable?
d_all'45'stable'63'_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> Bool
d_all'45'stable'63'_36 v0 ~v1 = du_all'45'stable'63'_36 v0
du_all'45'stable'63'_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> Bool
du_all'45'stable'63'_36 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_all'45'stable'63'_114
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.all-stable?-++
d_all'45'stable'63''45''43''43'_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45''43''43'_38 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.all-stable?-complete
d_all'45'stable'63''45'complete_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45'complete_40 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.all-stable?-sound
d_all'45'stable'63''45'sound_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'stable'63''45'sound_42 v0 ~v1
  = du_all'45'stable'63''45'sound_42 v0
du_all'45'stable'63''45'sound_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'stable'63''45'sound_42 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_all'45'stable'63''45'sound_136
      (coe v0) v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.bds
d_bds_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
  = coe MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_bds_634 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.blocks-stable
d_blocks'45'stable_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_blocks'45'stable_644
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.cata-body-stable
d_cata'45'body'45'stable_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'body'45'stable_48 ~v0 ~v1 = du_cata'45'body'45'stable_48
du_cata'45'body'45'stable_48 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'body'45'stable_48 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'body'45'stable_354
      v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.cata-dispatch-slot-stable
d_cata'45'dispatch'45'slot'45'stable_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'dispatch'45'slot'45'stable_50 v0 ~v1
  = du_cata'45'dispatch'45'slot'45'stable_50 v0
du_cata'45'dispatch'45'slot'45'stable_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'dispatch'45'slot'45'stable_50 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'dispatch'45'slot'45'stable_470
      (coe v0) v1 v2 v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.cata-trace-branching-stable
d_cata'45'trace'45'branching'45'stable_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'branching'45'stable_52 v0 ~v1
  = du_cata'45'trace'45'branching'45'stable_52 v0
du_cata'45'trace'45'branching'45'stable_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'branching'45'stable_52 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'branching'45'stable_436
      (coe v0) v1 v2 v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.cata-trace-const-stable
d_cata'45'trace'45'const'45'stable_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'const'45'stable_54 v0 ~v1
  = du_cata'45'trace'45'const'45'stable_54 v0
du_cata'45'trace'45'const'45'stable_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'const'45'stable_54 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'const'45'stable_374
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.cata-trace-linear-stable
d_cata'45'trace'45'linear'45'stable_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'linear'45'stable_56 v0 ~v1
  = du_cata'45'trace'45'linear'45'stable_56 v0
du_cata'45'trace'45'linear'45'stable_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'linear'45'stable_56 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'linear'45'stable_414
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.cata-trace-nat-stable
d_cata'45'trace'45'nat'45'stable_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'nat'45'stable_58 v0 ~v1
  = du_cata'45'trace'45'nat'45'stable_58 v0
du_cata'45'trace'45'nat'45'stable_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'nat'45'stable_58 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'nat'45'stable_394
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.ir-blocks-stable
d_ir'45'blocks'45'stable_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'blocks'45'stable_60 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'blocks'45'stable_738
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.ir-stable
d_ir'45'stable_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_62 v0 ~v1 = du_ir'45'stable_62 v0
du_ir'45'stable_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'stable_62 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'stable_524
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.ir-to-trace-lab-slot-stable
d_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 v0 ~v1
  = du_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 v0
du_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'lab'45'slot'45'stable_64 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'lab'45'slot'45'stable_868
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_66 v0 ~v1
  = du_ir'45'to'45'trace'45'slot'45'stable_66 v0
du_ir'45'to'45'trace'45'slot'45'stable_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'slot'45'stable_66 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_856
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.ir-to-trace-top-slot-stable
d_ir'45'to'45'trace'45'top'45'slot'45'stable_68 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'top'45'slot'45'stable_68 v0 ~v1
  = du_ir'45'to'45'trace'45'top'45'slot'45'stable_68 v0
du_ir'45'to'45'trace'45'top'45'slot'45'stable_68 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'top'45'slot'45'stable_68 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_ir'45'to'45'trace'45'top'45'slot'45'stable_882
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.rebuild-walk-stable
d_rebuild'45'walk'45'stable_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'walk'45'stable_70 v0 ~v1
  = du_rebuild'45'walk'45'stable_70 v0
du_rebuild'45'walk'45'stable_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'walk'45'stable_70 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_rebuild'45'walk'45'stable_296
      (coe v0) v1 v2 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.resuspend-stable
d_resuspend'45'stable_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_resuspend'45'stable_72 v0 ~v1 = du_resuspend'45'stable_72 v0
du_resuspend'45'stable_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_resuspend'45'stable_72 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_resuspend'45'stable_668
      (coe v0) v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.stable?
d_stable'63'_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> Bool
d_stable'63'_74 v0 ~v1 = du_stable'63'_74 v0
du_stable'63'_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> Bool
du_stable'63'_74 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_stable'63'_112
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.stable?-complete
d_stable'63''45'complete_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable'63''45'complete_76 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.stable?-sound
d_stable'63''45'sound_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_stable'63''45'sound_78 v0 ~v1 = du_stable'63''45'sound_78 v0
du_stable'63''45'sound_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_stable'63''45'sound_78 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_stable'63''45'sound_132
      (coe v0) v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.trc
d_trc_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_trc_80 ~v0 ~v1 = du_trc_80
du_trc_80 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_trc_80 v0 v1
  = coe MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_trc_100 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.visit-walk-stable
d_visit'45'walk'45'stable_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_visit'45'walk'45'stable_82 v0 ~v1
  = du_visit'45'walk'45'stable_82 v0
du_visit'45'walk'45'stable_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_visit'45'walk'45'stable_82 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_visit'45'walk'45'stable_234
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.∧-intro
d_'8743''45'intro_84 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'intro_84 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataIRSlotStable.∧-split
d_'8743''45'split_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_86 ~v0 ~v1 = du_'8743''45'split_86
du_'8743''45'split_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_86 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_'8743''45'split_128
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.BodyCorrect
d_BodyCorrect_92 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.CellAt
d_CellAt_96 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.CellLocsInRegions
d_CellLocsInRegions_98 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 -> ()
d_CellLocsInRegions_98 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF
d_ClosureValidWF_100 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureWellFormed
d_ClosureWellFormed_104 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                        a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.EnvAt
d_EnvAt_108 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRHeapBudget
d_IRHeapBudget_110 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF
d_IRResultAWF_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase
d_IRResultBase_118 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget
d_IRStackBudget_122 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InlValidWF
d_InlValidWF_128 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InlineRep
d_InlineRep_132 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InputPlace
d_InputPlace_134 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InrValidWF
d_InrValidWF_136 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.LocInRegions
d_LocInRegions_140 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.LocsInRegions
d_LocsInRegions_142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  ()
d_LocsInRegions_142 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.PairValidWF
d_PairValidWF_144 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.PayloadAt
d_PayloadAt_148 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.Place
d_Place_150 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.RecDispatcherWF
d_RecDispatcherWF_152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> ()
d_RecDispatcherWF_152 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ResultPlace
d_ResultPlace_154 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.SumTag
d_SumTag_156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_156 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_158 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.alloc-correct
d_alloc'45'correct_160 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_160 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.base
d_base_166 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692
d_base_166 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.before-frontier-monotone
d_before'45'frontier'45'monotone_168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_before'45'frontier'45'monotone_168 ~v0 ~v1
  = du_before'45'frontier'45'monotone_168
du_before'45'frontier'45'monotone_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_before'45'frontier'45'monotone_168 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_before'45'frontier'45'monotone_6962
      v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.body-cap-eq
d_body'45'cap'45'eq_170 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_170 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.body-capacity
d_body'45'capacity_172 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  Integer
d_body'45'capacity_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'capacity_1496
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.body-correct
d_body'45'correct_174 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800
d_body'45'correct_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'correct_1634
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.bump
d_bump_176 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump_176 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1170
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_178 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_178 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1298
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_180 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_180 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1246
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.code-before
d_code'45'before_186 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_code'45'before_186 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_code'45'before_1626
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.code-ptr
d_code'45'ptr_188 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_188 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.decomposeClosureWF
d_decomposeClosureWF_190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682
d_decomposeClosureWF_190 ~v0 ~v1 = du_decomposeClosureWF_190
du_decomposeClosureWF_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682
du_decomposeClosureWF_190 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1752
      v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.decomposeInlWF
d_decomposeInlWF_192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038
d_decomposeInlWF_192 ~v0 ~v1 = du_decomposeInlWF_192
du_decomposeInlWF_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038
du_decomposeInlWF_192 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeInlWF_2128
      v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.decomposeInrWF
d_decomposeInrWF_194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082
d_decomposeInrWF_194 ~v0 ~v1 = du_decomposeInrWF_194
du_decomposeInrWF_194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082
du_decomposeInrWF_194 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeInrWF_2170
      v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.decomposePairWF
d_decomposePairWF_196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906
d_decomposePairWF_196 ~v0 ~v1 = du_decomposePairWF_196
du_decomposePairWF_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906
du_decomposePairWF_196 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1948
      v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.derive-mem-preserved
d_derive'45'mem'45'preserved_198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved_198 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.derive-mem-preserved-at
d_derive'45'mem'45'preserved'45'at_200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved'45'at_200 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.env-before
d_env'45'before_204 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_env'45'before_204 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'before_1624
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.env-ptr
d_env'45'ptr_208 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_208 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.env-valid
d_env'45'valid_210 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_env'45'valid_210 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'valid_1632
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.evalᴰ
d_eval'7472'_212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_212 ~v0 v1 = du_eval'7472'_212 v1
du_eval'7472'_212 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_212 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval'7472'_24
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.execute
d_execute_214 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_214 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_execute_1514
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.final-alloc
d_final'45'alloc_216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_final'45'alloc_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_216 v9 v10
du_final'45'alloc_216 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_final'45'alloc_216 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1200
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.final-state
d_final'45'state_218 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_218 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1166
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.frame-preserved
d_frame'45'preserved_220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_220 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.frontier-slot-stable
d_frontier'45'slot'45'stable_222 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_222 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1256
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.heap-budget
d_heap'45'budget_224 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_heap'45'budget_224 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1294
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.heap-inv
d_heap'45'inv_226 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710
d_heap'45'inv_226 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.heap-monotone
d_heap'45'monotone_228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_228 v9
du_heap'45'monotone_228 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_228 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1304
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.heap-preserved-of
d_heap'45'preserved'45'of_230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'preserved'45'of_230 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.inline-sv
d_inline'45'sv_238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_590 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_238 ~v0 ~v1 = du_inline'45'sv_238
du_inline'45'sv_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_590 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_238 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_600
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.input-read
d_input'45'read_240 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'read_240 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.input-sv
d_input'45'sv_242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_input'45'sv_242 ~v0 ~v1 = du_input'45'sv_242
du_input'45'sv_242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_input'45'sv_242 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_input'45'sv_1844
      v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.inputPlace-transport
d_inputPlace'45'transport_244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812
d_inputPlace'45'transport_244 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inputPlace'45'transport_5592
      (coe v0) (coe v1) v2 v3 v5 v6 v7 v8 v9 v10 v12 v13
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ir-returns
d_ir'45'returns_246 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_ir'45'returns_246 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ir'45'returns_1180
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.irresult-mem-preserved
d_irresult'45'mem'45'preserved_248 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irresult'45'mem'45'preserved_248 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.loc-mem-eq-from-regions
d_loc'45'mem'45'eq'45'from'45'regions_258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_LocInRegions_5654 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loc'45'mem'45'eq'45'from'45'regions_258 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.mEnv
d_mEnv_260 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_260 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_mEnv_1630
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_262 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_262 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1300
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.max-heap-ref-written
d_max'45'heap'45'ref'45'written_264 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_max'45'heap'45'ref'45'written_264 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1296
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_266 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_266 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1302
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.max-slot-geq-final
d_max'45'slot'45'geq'45'final_268 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_268 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1248
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_270 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_270 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1250
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.max-slot-written
d_max'45'slot'45'written_272 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_max'45'slot'45'written_272 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1242
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.mem-preserved-before
d_mem'45'preserved'45'before_274 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_274 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.mem-preserved-compose
d_mem'45'preserved'45'compose_276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'compose_276 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.mem-preserved-from-tnhw
d_mem'45'preserved'45'from'45'tnhw_278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'from'45'tnhw_278 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.mk-IRResultAWF-via-bump
d_mk'45'IRResultAWF'45'via'45'bump_280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726
d_mk'45'IRResultAWF'45'via'45'bump_280 ~v0 ~v1
  = du_mk'45'IRResultAWF'45'via'45'bump_280
du_mk'45'IRResultAWF'45'via'45'bump_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726
du_mk'45'IRResultAWF'45'via'45'bump_280 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
                                        v24 v25
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_mk'45'IRResultAWF'45'via'45'bump_784
      v8 v10 v11 v16 v17 v18 v21 v23 v24 v25
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.not-halted
d_not'45'halted_282 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_282 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.obs-budget
d_obs'45'budget_284 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_obs'45'budget_284 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1178
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.payload-read
d_payload'45'read_290 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'read_290 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.payload-sv
d_payload'45'sv_292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_payload'45'sv_292 ~v0 ~v1 = du_payload'45'sv_292
du_payload'45'sv_292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_payload'45'sv_292 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_payload'45'sv_2000
      v3 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.place-rax
d_place'45'rax_294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_place'45'rax_294 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.place-sv
d_place'45'sv_296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_place'45'sv_296 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_place'45'sv_660
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.prim-sv
d_prim'45'sv_298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_298 ~v0 ~v1 = du_prim'45'sv_298
du_prim'45'sv_298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_298 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_582
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.reclaim-alloc
d_reclaim'45'alloc_300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_reclaim'45'alloc_300 ~v0 ~v1 = du_reclaim'45'alloc_300
du_reclaim'45'alloc_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_reclaim'45'alloc_300 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_reclaim'45'alloc_6642
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.reclaim-preserves-frontier
d_reclaim'45'preserves'45'frontier_302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_reclaim'45'preserves'45'frontier_302 ~v0 ~v1
  = du_reclaim'45'preserves'45'frontier_302
du_reclaim'45'preserves'45'frontier_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_reclaim'45'preserves'45'frontier_302 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_reclaim'45'preserves'45'frontier_6656
      v3 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.result-place
d_result'45'place_308 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_result'45'place_308 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1182
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.scratch-bounded
d_scratch'45'bounded_310 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_310 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1268
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.scratch-budget
d_scratch'45'budget_312 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_scratch'45'budget_312 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1266
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.slot-monotone
d_slot'45'monotone_314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_314 v9
du_slot'45'monotone_314 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_314 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1270
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_316 v9 v10
du_slot'45'stays'45'in'45'budget_316 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_316 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1272
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1170
         (coe
            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.stack-budget
d_stack'45'budget_318 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_stack'45'budget_318 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1244
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.stack-inv
d_stack'45'inv_320 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702
d_stack'45'inv_320 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.sucLoc-before
d_sucLoc'45'before_322 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_322 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1628
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace
d_trace_324 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_trace_324 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1168
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace-correct
d_trace'45'correct_326 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_326 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_328 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_328 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_330 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_330 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1198
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace-preserves-halted
d_trace'45'preserves'45'halted_332 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_332 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_334 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_334 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1260
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_336 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_336 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1264
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace-twf
d_trace'45'twf_338 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_trace'45'twf_338 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1190
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace-writes-above
d_trace'45'writes'45'above_340 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'writes'45'above_340 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1258
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.trace-writes-below
d_trace'45'writes'45'below_342 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'writes'45'below_342 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1262
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.transport-SumTag
d_transport'45'SumTag_344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_transport'45'SumTag_344 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.valid-primitive-wf
d_valid'45'primitive'45'wf_366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_valid'45'primitive'45'wf_366 ~v0 ~v1
  = du_valid'45'primitive'45'wf_366
du_valid'45'primitive'45'wf_366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_valid'45'primitive'45'wf_366 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'primitive'45'wf_632
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.valid-to-validWF-unit
d_valid'45'to'45'validWF'45'unit_368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_valid'45'to'45'validWF'45'unit_368 ~v0 ~v1
  = du_valid'45'to'45'validWF'45'unit_368
du_valid'45'to'45'validWF'45'unit_368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_valid'45'to'45'validWF'45'unit_368 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'to'45'validWF'45'unit_2206
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-alloc-advance
d_validityWF'45'alloc'45'advance_376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'alloc'45'advance_376 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'alloc'45'advance_4100
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v10
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_378 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'frontier'45'advance_378 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4440
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v11 v12 v13
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-mem-only
d_validityWF'45'mem'45'only_380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'mem'45'only_380 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'only_2222
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'mem'45'preserved_382 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-mem-preserved-excluding
d_validityWF'45'mem'45'preserved'45'excluding_384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'mem'45'preserved'45'excluding_384 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_validityWF'45'mem'45'preserved'45'excluding_5646
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-mem-preserved-in-regions
d_validityWF'45'mem'45'preserved'45'in'45'regions_386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'mem'45'preserved'45'in'45'regions_386 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_validityWF'45'mem'45'preserved'45'in'45'regions_6636
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-mem-preserved-in-regions-strong
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_388 v0
                                                                v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                v12 v13 v14 v15 v16 v17 v18 v19 v20
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042
      (coe v0) (coe v1) v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v19 v20
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-reclaim
d_validityWF'45'reclaim_390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'reclaim_390 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'reclaim_6740
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v10 v12
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-trace-preserves
d_validityWF'45'trace'45'preserves_392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'trace'45'preserves_392 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'trace'45'preserves_6880
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'with'45'bf'45'transfer_394 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'with'45'bf'45'transfer_4856
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v10 v11
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-write-at-frontier
d_validityWF'45'write'45'at'45'frontier_396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'write'45'at'45'frontier_396 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'at'45'frontier_2610
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-write-at-suc-frontier
d_validityWF'45'write'45'at'45'suc'45'frontier_398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'write'45'at'45'suc'45'frontier_398 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'at'45'suc'45'frontier_2982
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-write-sv-at-frontier
d_validityWF'45'write'45'sv'45'at'45'frontier_400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'write'45'sv'45'at'45'frontier_400 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'sv'45'at'45'frontier_3354
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.validityWF-write-sv-at-suc-frontier
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_402 v0 v1 v2
                                                         v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ιᶠ
d_ι'7584'_404 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_ι'7584'_404 ~v0 ~v1 = du_ι'7584'_404
du_ι'7584'_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
du_ι'7584'_404
  = coe MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_ι'7584'_26
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.μ-validity-in-regions-stub
d_μ'45'validity'45'in'45'regions'45'stub_406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_μ'45'validity'45'in'45'regions'45'stub_406 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_μ'45'validity'45'in'45'regions'45'stub_5984
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ν-validity-in-regions-stub
d_ν'45'validity'45'in'45'regions'45'stub_408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_ν'45'validity'45'in'45'regions'45'stub_408 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ν'45'validity'45'in'45'regions'45'stub_6010
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.BodyCorrect.body-cap-eq
d_body'45'cap'45'eq_412 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_412 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.BodyCorrect.body-capacity
d_body'45'capacity_414 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  Integer
d_body'45'capacity_414 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'capacity_1496
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.BodyCorrect.execute
d_execute_416 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_416 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_execute_1514
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF.EnvType
d_EnvType_426 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_426 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_EnvType_1716
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF.body
d_body_428 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_body_428 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body_1718
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF.body-label
d_body'45'label_430 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_430 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'label_1722
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF.code-ptr
d_code'45'ptr_432 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_432 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF.env
d_env_434 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  AgdaAny
d_env_434 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env_1720 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF.env-at
d_env'45'at_436 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1648
d_env'45'at_436 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'at_1726
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_438 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_438 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF.loc-mode
d_loc'45'mode_440 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  AgdaAny
d_loc'45'mode_440 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_loc'45'mode_1724
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_442 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_442 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1730
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureWellFormed.body-correct
d_body'45'correct_446 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800
d_body'45'correct_446 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'correct_1634
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureWellFormed.code-before
d_code'45'before_448 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_code'45'before_448 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_code'45'before_1626
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureWellFormed.code-ptr
d_code'45'ptr_450 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_450 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureWellFormed.env-before
d_env'45'before_452 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_env'45'before_452 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'before_1624
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureWellFormed.env-ptr
d_env'45'ptr_454 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_454 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureWellFormed.env-valid
d_env'45'valid_456 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_env'45'valid_456 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'valid_1632
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureWellFormed.mEnv
d_mEnv_458 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_458 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_mEnv_1630
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.ClosureWellFormed.sucLoc-before
d_sucLoc'45'before_460 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_460 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1628
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRHeapBudget.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_470 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_470 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1298
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRHeapBudget.heap-budget
d_heap'45'budget_472 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  Integer
d_heap'45'budget_472 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1294
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRHeapBudget.heap-monotone
d_heap'45'monotone_474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_474 ~v0 ~v1 = du_heap'45'monotone_474
du_heap'45'monotone_474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_474 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1304
      v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_476 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_476 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1300
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-written
d_max'45'heap'45'ref'45'written_478 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  Integer
d_max'45'heap'45'ref'45'written_478 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1296
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRHeapBudget.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_480 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_480 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1302
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.alloc-correct
d_alloc'45'correct_484 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_484 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.base
d_base_486 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692
d_base_486 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.bump
d_bump_488 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump_488 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1170
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_490 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_490 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1298
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_492 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_492 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1246
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.final-alloc
d_final'45'alloc_494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_final'45'alloc_494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_494 v9 v10
du_final'45'alloc_494 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_final'45'alloc_494 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1200
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.final-state
d_final'45'state_496 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_496 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1166
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.frame-preserved
d_frame'45'preserved_498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_498 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.frontier-slot-stable
d_frontier'45'slot'45'stable_500 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_500 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1256
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.heap-budget
d_heap'45'budget_502 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_heap'45'budget_502 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1294
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.heap-inv
d_heap'45'inv_504 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710
d_heap'45'inv_504 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.heap-monotone
d_heap'45'monotone_506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_506 v9
du_heap'45'monotone_506 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_506 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1304
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.ir-returns
d_ir'45'returns_508 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_ir'45'returns_508 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ir'45'returns_1180
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_510 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_510 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1300
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.max-heap-ref-written
d_max'45'heap'45'ref'45'written_512 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_max'45'heap'45'ref'45'written_512 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1296
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_514 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_514 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1302
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.max-slot-geq-final
d_max'45'slot'45'geq'45'final_516 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_516 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1248
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_518 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_518 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1250
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.max-slot-written
d_max'45'slot'45'written_520 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_max'45'slot'45'written_520 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1242
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.mem-preserved-before
d_mem'45'preserved'45'before_522 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_522 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.not-halted
d_not'45'halted_524 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_524 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.obs-budget
d_obs'45'budget_526 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_obs'45'budget_526 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1178
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.result-place
d_result'45'place_528 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_result'45'place_528 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1182
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.scratch-bounded
d_scratch'45'bounded_530 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_530 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1268
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.scratch-budget
d_scratch'45'budget_532 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_scratch'45'budget_532 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1266
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.slot-monotone
d_slot'45'monotone_534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_534 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_534 v9
du_slot'45'monotone_534 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_534 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1270
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_536 v9 v10
du_slot'45'stays'45'in'45'budget_536 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_536 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1272
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1170
         (coe
            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.stack-budget
d_stack'45'budget_538 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_stack'45'budget_538 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1244
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.stack-inv
d_stack'45'inv_540 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702
d_stack'45'inv_540 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace
d_trace_542 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_trace_542 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1168
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace-correct
d_trace'45'correct_544 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_544 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_546 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_546 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_548 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_548 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1198
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace-preserves-halted
d_trace'45'preserves'45'halted_550 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_550 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_552 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_552 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1260
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_554 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_554 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1264
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace-twf
d_trace'45'twf_556 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_trace'45'twf_556 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1190
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace-writes-above
d_trace'45'writes'45'above_558 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'writes'45'above_558 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1258
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultAWF.trace-writes-below
d_trace'45'writes'45'below_560 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'writes'45'below_560 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1262
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.alloc-correct
d_alloc'45'correct_564 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_564 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.bump
d_bump_566 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump_566 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1170
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.final-alloc
d_final'45'alloc_568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_final'45'alloc_568 ~v0 ~v1 = du_final'45'alloc_568
du_final'45'alloc_568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_final'45'alloc_568 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1200
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.final-state
d_final'45'state_570 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_570 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1166
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.frame-preserved
d_frame'45'preserved_572 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_572 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.ir-returns
d_ir'45'returns_574 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  AgdaAny
d_ir'45'returns_574 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ir'45'returns_1180
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.mem-preserved-before
d_mem'45'preserved'45'before_576 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_576 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.not-halted
d_not'45'halted_578 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_578 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.obs-budget
d_obs'45'budget_580 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  Integer
d_obs'45'budget_580 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1178
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.result-place
d_result'45'place_582 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_result'45'place_582 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1182
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.trace
d_trace_584 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_trace_584 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1168
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.trace-correct
d_trace'45'correct_586 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_586 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_588 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_588 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_590 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_590 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1198
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.trace-preserves-halted
d_trace'45'preserves'45'halted_592 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_592 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRResultBase.trace-twf
d_trace'45'twf_594 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_trace'45'twf_594 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1190
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_598 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_598 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1246
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.frontier-slot-stable
d_frontier'45'slot'45'stable_600 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_600 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1256
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.max-slot-geq-final
d_max'45'slot'45'geq'45'final_602 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_602 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1248
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_604 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_604 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1250
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.max-slot-written
d_max'45'slot'45'written_606 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  Integer
d_max'45'slot'45'written_606 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1242
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.scratch-bounded
d_scratch'45'bounded_608 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_608 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1268
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.scratch-budget
d_scratch'45'budget_610 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  Integer
d_scratch'45'budget_610 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1266
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.slot-monotone
d_slot'45'monotone_612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_612 ~v0 ~v1 = du_slot'45'monotone_612
du_slot'45'monotone_612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_612 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1270
      v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_614 ~v0 ~v1
  = du_slot'45'stays'45'in'45'budget_614
du_slot'45'stays'45'in'45'budget_614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_614 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1272
      v1 v2 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.stack-budget
d_stack'45'budget_616 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  Integer
d_stack'45'budget_616 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1244
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_618 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_618 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1260
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_620 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_620 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1264
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.trace-writes-above
d_trace'45'writes'45'above_622 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  AgdaAny
d_trace'45'writes'45'above_622 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1258
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.IRStackBudget.trace-writes-below
d_trace'45'writes'45'below_624 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  AgdaAny
d_trace'45'writes'45'below_624 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1262
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InlValidWF.a
d_a_628 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038 ->
  AgdaAny
d_a_628 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_a_2060 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InlValidWF.payload
d_payload_630 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968
d_payload_630 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_payload_2064
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InlValidWF.sucLoc-before
d_sucLoc'45'before_632 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_632 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_2062
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InlValidWF.v-is-inl
d_v'45'is'45'inl_634 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_634 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InrValidWF.b
d_b_652 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082 ->
  AgdaAny
d_b_652 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_b_2104 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InrValidWF.payload
d_payload_654 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968
d_payload_654 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_payload_2108
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InrValidWF.sucLoc-before
d_sucLoc'45'before_656 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_656 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_2106
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.InrValidWF.v-is-inr
d_v'45'is'45'inr_658 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_658 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.PairValidWF.fst-cell
d_fst'45'cell_672 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612
d_fst'45'cell_672 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.PairValidWF.snd-cell
d_snd'45'cell_674 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612
d_snd'45'cell_674 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1930
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ClosureWellFormedDef.PairValidWF.sucLoc-before
d_sucLoc'45'before_676 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_676 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1926
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Nat._+_
d__'43'__730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> Integer
d__'43'__730 ~v0 ~v1 = du__'43'__730
du__'43'__730 :: Integer -> Integer -> Integer
du__'43'__730 = coe addInt
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base._++_
d__'43''43'__734 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d__'43''43'__734 ~v0 ~v1 = du__'43''43'__734
du__'43''43'__734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'43''43'__734 v0 v1 v2 v3
  = coe MAlonzo.Code.Data.List.Base.du__'43''43'__32 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base._<_
d__'60'__742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> ()
d__'60'__742 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base._×_
d__'215'__746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'__746 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Nat._-_
d__'45'__756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> Integer
d__'45'__756 ~v0 ~v1 = du__'45'__756
du__'45'__756 :: Integer -> Integer -> Integer
du__'45'__756 = coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
-- Once.CCC.Codegen.IRObsCorrect.Interface._.HeapAddress._≟HL_
d__'8799'HL__760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'HL__760 ~v0 ~v1 = du__'8799'HL__760
du__'8799'HL__760 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'HL__760
  = coe MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Equality._≡_
d__'8801'__764 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Core._≢_
d__'8802'__768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> ()
d__'8802'__768 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base._≤_
d__'8804'__770 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._._.++-assoc
d_'43''43''45'assoc_774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'assoc_774 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.++⁺
d_'43''43''8314'_778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_'43''43''8314'_778 ~v0 ~v1 = du_'43''43''8314'_778
du_'43''43''8314'_778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_'43''43''8314'_778 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      v4 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.++⁻
d_'43''43''8315'_780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''43''8315'_780 ~v0 ~v1 = du_'43''43''8315'_780
du_'43''43''8315'_780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'43''43''8315'_780 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
      v4 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.+-assoc
d_'43''45'assoc_784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_784 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.+-comm
d_'43''45'comm_786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_786 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.+-identityʳ
d_'43''45'identity'691'_788 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691'_788 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.+-suc
d_'43''45'suc_790 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'suc_790 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.<-irrefl
d_'60''45'irrefl_792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_792 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.<-trans
d_'60''45'trans_794 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans_794 ~v0 ~v1 = du_'60''45'trans_794
du_'60''45'trans_794 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'trans_794 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122 v1 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.<-≤-trans
d_'60''45''8804''45'trans_796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45''8804''45'trans_796 ~v0 ~v1
  = du_'60''45''8804''45'trans_796
du_'60''45''8804''45'trans_796 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45''8804''45'trans_796 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.AbstractInstr
d_AbstractInstr_800 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.AbstractTrace
d_AbstractTrace_802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> ()
d_AbstractTrace_802 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.All.All
d_All_806 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.IR.AllocMode
d_AllocMode_810 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.AllocState
d_AllocState_812 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Word.Carrier
d_Carrier_828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> ()
d_Carrier_828 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Decimal.Decimal
d_Decimal_834 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Info.EffectShape
d_EffectShape_840 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Type.FitsInReg
d_FitsInReg_848 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.IRTy.FitsInRegI
d_FitsInRegI_852 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.FrameSemantics
d_FrameSemantics_856 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.HeapAddress.HeapLocation
d_HeapLocation_868 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.HeapAddress.HeapRef
d_HeapRef_872 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.IR.IR
d_IR_876 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.IRTy.IRTy
d_IRTy_878 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Label.LabelId
d_LabelId_892 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.List.List
d_List_898 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.LocState
d_LocState_900 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Maybe.Maybe
d_Maybe_906 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Trace.SigOpEvent
d_SigOpEvent_928 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Info.SigOpInfo
d_SigOpInfo_932 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.StoredValue
d_StoredValue_938 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Type.Type
d_Type_940 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Locations.ValueLocation
d_ValueLocation_948 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.IRTy.WellFormedFI
d_WellFormedFI_950 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.IRTy.WellFormedFI-irrelevant
d_WellFormedFI'45'irrelevant_952 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedFI'45'irrelevant_952 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.block-layout
d_block'45'layout_962 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_block'45'layout_962 ~v0 ~v1 = du_block'45'layout_962
du_block'45'layout_962 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_block'45'layout_962
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'layout_2330
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base.case_of_
d_case_of__968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_case_of__968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_case_of__968 v6 v7
du_case_of__968 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_case_of__968 v0 v1 = coe v1 v0
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Core.cong
d_cong_970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_cong_970 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Core.cong₂
d_cong'8322'_972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_cong'8322'_972 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AllocState.current-frame
d_current'45'frame_978 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> AgdaAny
d_current'45'frame_978 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Info.effect
d_effect_982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126
d_effect_982 ~v0 ~v1 = du_effect_982
du_effect_982 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126
du_effect_982 v0 v1 v2
  = coe MAlonzo.Code.Once.SigOp.Info.du_effect_352 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._._.exec-abstract-preserves-next-slot
d_exec'45'abstract'45'preserves'45'next'45'slot_986 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'next'45'slot_986 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Type.fits-in-reg?
d_fits'45'in'45'reg'63'_1000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200
d_fits'45'in'45'reg'63'_1000 ~v0 ~v1
  = du_fits'45'in'45'reg'63'_1000
du_fits'45'in'45'reg'63'_1000 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200
du_fits'45'in'45'reg'63'_1000
  = coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LocState.halted
d_halted_1010 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_halted_1010 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_422 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.HeapLocation.heap-ref
d_heap'45'ref_1016 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
d_heap'45'ref_1016 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Size.ir-size
d_ir'45'size_1046 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'size_1046 ~v0 ~v1 = du_ir'45'size_1046
du_ir'45'size_1046 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'size_1046 = coe MAlonzo.Code.Once.IR.Size.d_ir'45'size_10
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base.length
d_length_1052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer
d_length_1052 ~v0 ~v1 = du_length_1052
du_length_1052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer
du_length_1052 v0 v1
  = coe MAlonzo.Code.Data.List.Base.du_length_268
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.length-++
d_length'45''43''43'_1056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''43''43'_1056 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base.map
d_map_1064 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_map_1064 ~v0 ~v1 = du_map_1064
du_map_1064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_map_1064 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Data.List.Base.du_map_22 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base.map
d_map_1070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_map_1070 ~v0 ~v1 = du_map_1070
du_map_1070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_map_1070 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Data.Maybe.Base.du_map_64 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.m≤m+n
d_m'8804'm'43'n_1076 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'm'43'n_1076 ~v0 ~v1 = du_m'8804'm'43'n_1076
du_m'8804'm'43'n_1076 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'm'43'n_1076 v0 v1
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 v0
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.m≤n+m
d_m'8804'n'43'm_1078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43'm_1078 ~v0 ~v1 = du_m'8804'n'43'm_1078
du_m'8804'n'43'm_1078 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'43'm_1078 v0 v1
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636 v0
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.n<1+n
d_n'60'1'43'n_1080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'1'43'n_1080 ~v0 ~v1 = du_n'60'1'43'n_1080
du_n'60'1'43'n_1080 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'60'1'43'n_1080
  = coe MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AllocState.next-heap-ref
d_next'45'heap'45'ref_1082 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'heap'45'ref_1082 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AllocState.next-slot
d_next'45'slot_1084 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'slot_1084 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_590 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.n≤1+n
d_n'8804'1'43'n_1088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'1'43'n_1088 ~v0 ~v1 = du_n'8804'1'43'n_1088
du_n'8804'1'43'n_1088 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'8804'1'43'n_1088
  = coe MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TraceMonad.projTrace
d_projTrace_1094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_projTrace_1094 ~v0 ~v1 = du_projTrace_1094
du_projTrace_1094 ::
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_projTrace_1094 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_868 v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Σ.fst
d_fst_1098 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_1098 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Σ.snd
d_snd_1100 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_1100 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.readReg
d_readReg_1102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readReg_1102 ~v0 ~v1 = du_readReg_1102
du_readReg_1102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readReg_1102 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.HeapRef.ref-id
d_ref'45'id_1106 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 -> Integer
d_ref'45'id_1106 v0
  = coe MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LocState.regs
d_regs_1112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs_1112 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Decimal.round
d_round_1116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_round_1116 ~v0 ~v1 = du_round_1116
du_round_1116 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
du_round_1116 = coe MAlonzo.Code.Once.Float.Decimal.d_round_174
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Core.subst
d_subst_1126 ::
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
d_subst_1126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_subst_1126 v9
du_subst_1126 :: AgdaAny -> AgdaAny
du_subst_1126 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Core.subst₂
d_subst'8322'_1128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_subst'8322'_1128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 ~v13 v14
  = du_subst'8322'_1128 v14
du_subst'8322'_1128 :: AgdaAny -> AgdaAny
du_subst'8322'_1128 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Interface._.HeapAddress.sucHL
d_sucHL_1134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_sucHL_1134 ~v0 ~v1 = du_sucHL_1134
du_sucHL_1134 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_sucHL_1134 = coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.sucLoc
d_sucLoc_1136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sucLoc_1136 ~v0 ~v1 = du_sucLoc_1136
du_sucLoc_1136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sucLoc_1136 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.sv-as-loc
d_sv'45'as'45'loc_1138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1138 ~v0 ~v1 = du_sv'45'as'45'loc_1138
du_sv'45'as'45'loc_1138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1138 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Core.sym
d_sym_1140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1140 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base.take
d_take_1142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> [AgdaAny] -> [AgdaAny]
d_take_1142 ~v0 ~v1 = du_take_1142
du_take_1142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> [AgdaAny] -> [AgdaAny]
du_take_1142 v0 v1 v2 v3
  = coe MAlonzo.Code.Data.List.Base.du_take_530 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Core.trans
d_trans_1146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1146 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.writeReg
d_writeReg_1154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_writeReg_1154 ~v0 ~v1 = du_writeReg_1154
du_writeReg_1154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_writeReg_1154 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.writeReg-preserves
d_writeReg'45'preserves_1156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_1156 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SMCore.writeReg-same
d_writeReg'45'same_1158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_1158 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Label.ℓ
d_ℓ_1166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_ℓ_1166 ~v0 ~v1 = du_ℓ_1166
du_ℓ_1166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_ℓ_1166 = coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Nat.Nat
d_Nat_1168 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Int.Int
d_Int_1172 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base.∃
d_'8707'_1174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> ()
d_'8707'_1174 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Base.∃-syntax
d_'8707''45'syntax_1176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> ()
d_'8707''45'syntax_1176 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.≤-<-trans
d_'8804''45''60''45'trans_1178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45''60''45'trans_1178 ~v0 ~v1
  = du_'8804''45''60''45'trans_1178
du_'8804''45''60''45'trans_1178 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45''60''45'trans_1178 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.≤-refl
d_'8804''45'refl_1180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'refl_1180 ~v0 ~v1 = du_'8804''45'refl_1180
du_'8804''45'refl_1180 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'refl_1180
  = coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.≤-reflexive
d_'8804''45'reflexive_1182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'reflexive_1182 ~v0 ~v1 = du_'8804''45'reflexive_1182
du_'8804''45'reflexive_1182 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'reflexive_1182 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896 v0
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Properties.≤-trans
d_'8804''45'trans_1184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'trans_1184 ~v0 ~v1 = du_'8804''45'trans_1184
du_'8804''45'trans_1184 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'trans_1184 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Empty.⊥
d_'8869'_1188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> ()
d_'8869'_1188 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Empty.⊥-elim
d_'8869''45'elim_1190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim_1190 ~v0 ~v1 = du_'8869''45'elim_1190
du_'8869''45'elim_1190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
du_'8869''45'elim_1190 v0 v1 v2
  = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
-- Once.CCC.Codegen.IRObsCorrect.Interface._.IRTy.⌊_⌋
d_'8970'_'8971'_1192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_'8970'_'8971'_1192 ~v0 ~v1 = du_'8970'_'8971'_1192
du_'8970'_'8971'_1192 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
du_'8970'_'8971'_1192
  = coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
-- Once.CCC.Codegen.IRObsCorrect.Interface._.IRTy.⟦_,_⟧-baseI
d_'10214'_'44'_'10215''45'baseI_1194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  () -> () -> MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'44'_'10215''45'baseI_1194 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ValueDomain.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_1198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_1198 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.IRTy.⟦_⟧TI
d_'10214'_'10215'TI_1200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_'10214'_'10215'TI_1200 ~v0 ~v1 = du_'10214'_'10215'TI_1200
du_'10214'_'10215'TI_1200 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
du_'10214'_'10215'TI_1200
  = coe MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.AllI
d_AllI_1214 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_AllI_1214 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.BodyRunner
d_BodyRunner_1216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_1216 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.call-sigop-ans
d_call'45'sigop'45'ans_1218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'ans_1218 ~v0 ~v1 = du_call'45'sigop'45'ans_1218
du_call'45'sigop'45'ans_1218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_call'45'sigop'45'ans_1218
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'ans_2940
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.call-sigop-ans-at
d_call'45'sigop'45'ans'45'at_1220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'ans'45'at_1220 ~v0 ~v1
  = du_call'45'sigop'45'ans'45'at_1220
du_call'45'sigop'45'ans'45'at_1220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_call'45'sigop'45'ans'45'at_1220
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'ans'45'at_2910
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.call-sigop-dec
d_call'45'sigop'45'dec_1222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_call'45'sigop'45'dec_1222 ~v0 ~v1 = du_call'45'sigop'45'dec_1222
du_call'45'sigop'45'dec_1222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_call'45'sigop'45'dec_1222
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'dec_2962
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.call-sigop-output
d_call'45'sigop'45'output_1224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'output_1224 ~v0 ~v1
  = du_call'45'sigop'45'output_1224
du_call'45'sigop'45'output_1224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_call'45'sigop'45'output_1224
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'output_2990
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.call-sigop-val
d_call'45'sigop'45'val_1226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'val_1226 ~v0 ~v1 = du_call'45'sigop'45'val_1226
du_call'45'sigop'45'val_1226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_call'45'sigop'45'val_1226
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'val_2974
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.case-tag-at
d_case'45'tag'45'at_1228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_case'45'tag'45'at_1228 ~v0 ~v1 = du_case'45'tag'45'at_1228
du_case'45'tag'45'at_1228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_case'45'tag'45'at_1228 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_3134 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.combine-typed
d_combine'45'typed_1230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_1230 ~v0 ~v1 = du_combine'45'typed_1230
du_combine'45'typed_1230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_1230 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_combine'45'typed_2694 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.decode-at
d_decode'45'at_1232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_decode'45'at_1232 ~v0 ~v1 = du_decode'45'at_1232
du_decode'45'at_1232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_decode'45'at_1232 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_decode'45'at_2868 v1 v2 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.events-at-arg
d_events'45'at'45'arg_1234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_events'45'at'45'arg_1234 ~v0 ~v1 = du_events'45'at'45'arg_1234
du_events'45'at'45'arg_1234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_events'45'at'45'arg_1234 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_events'45'at'45'arg_2884 v1
      v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-abstract
d_exec'45'abstract_1236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_1236 ~v0 ~v1 = du_exec'45'abstract_1236
du_exec'45'abstract_1236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_1236
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_1238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_1238 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_1240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_1240 ~v0 ~v1
  = du_exec'45'case'45'dispatch_1240
du_exec'45'case'45'dispatch_1240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'case'45'dispatch_1240
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_3234
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_1242 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_1242 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_1244 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_1244 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_1246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_1246 ~v0 ~v1
  = du_exec'45'load'45'from'45'slot'45'with'45'value_1246
du_exec'45'load'45'from'45'slot'45'with'45'value_1246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_1246 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2636
      v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-loop
d_exec'45'loop_1248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_1248 ~v0 ~v1 = du_exec'45'loop_1248
du_exec'45'loop_1248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop_1248
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'loop_3232
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-loop-run
d_exec'45'loop'45'run_1250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_1250 ~v0 ~v1 = du_exec'45'loop'45'run_1250
du_exec'45'loop'45'run_1250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_1250 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_3162 v1
      v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_1252 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_1252 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_1254 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_1254 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_1256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_1256 ~v0 ~v1
  = du_exec'45'restore'45'input'45'with'45'value_1256
du_exec'45'restore'45'input'45'with'45'value_1256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_1256 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2648
      v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_1258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_1258 ~v0 ~v1
  = du_exec'45'sigop'45'halts_1258
du_exec'45'sigop'45'halts_1258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts_1258 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_3126
      v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_1260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_1260 ~v0 ~v1
  = du_exec'45'sigop'45'halts'45'of_1260
du_exec'45'sigop'45'halts'45'of_1260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts'45'of_1260 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_3120
      v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_1262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_1262 ~v0 ~v1
  = du_exec'45'sigop'45'output_1262
du_exec'45'sigop'45'output_1262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output_1262
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_3110
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_1264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_1264 ~v0 ~v1
  = du_exec'45'sigop'45'output'45'of_1264
du_exec'45'sigop'45'output'45'of_1264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_1264
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_3068
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-trace
d_exec'45'trace_1266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_1266 ~v0 ~v1 = du_exec'45'trace_1266
du_exec'45'trace_1266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace_1266
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3230
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_1268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_1268 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_1270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_1270 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_1272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_1272 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_1274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_1274 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_1276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_1276 ~v0 ~v1
  = du_exec'45'tree'45'flat'45'equiv'45'simple_1276
du_exec'45'tree'45'flat'45'equiv'45'simple_1276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_1276 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'tree'45'flat'45'equiv'45'simple_4260
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_1278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_1278 ~v0 ~v1
  = du_exec'45'tree'45'trace_1278
du_exec'45'tree'45'trace_1278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'tree'45'trace_1278
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'tree'45'trace_3870
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_1280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_1280 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_1282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_1282 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_1284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_1284 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_1286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_1286 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_1288 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_1288 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.getTag
d_getTag_1290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> Maybe Integer
d_getTag_1290 ~v0 ~v1 = du_getTag_1290
du_getTag_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> Maybe Integer
du_getTag_1290 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_getTag_3846 v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.lit-value
d_lit'45'value_1292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 -> AgdaAny -> AgdaAny
d_lit'45'value_1292 ~v0 ~v1 = du_lit'45'value_1292
du_lit'45'value_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 -> AgdaAny -> AgdaAny
du_lit'45'value_1292 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_lit'45'value_3222 v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.loop-fuel
d_loop'45'fuel_1294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_loop'45'fuel_1294 ~v0 ~v1 = du_loop'45'fuel_1294
du_loop'45'fuel_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
du_loop'45'fuel_1294 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'fuel_3132
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_1296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_loop'45'reanchor'45'alloc_1296 ~v0 ~v1
  = du_loop'45'reanchor'45'alloc_1296
du_loop'45'reanchor'45'alloc_1296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_loop'45'reanchor'45'alloc_1296 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_3156
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.loop-reanchor-loc
d_loop'45'reanchor'45'loc_1298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_loop'45'reanchor'45'loc_1298 ~v0 ~v1
  = du_loop'45'reanchor'45'loc_1298
du_loop'45'reanchor'45'loc_1298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_loop'45'reanchor'45'loc_1298 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_3150
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.machine-events
d_machine'45'events_1300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_machine'45'events_1300 ~v0 ~v1 = du_machine'45'events_1300
du_machine'45'events_1300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_machine'45'events_1300 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_machine'45'events_2898 v1
      v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_1302 ::
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
d_pure'45'sigop'45'out'45'aux_1302 ~v0 ~v1
  = du_pure'45'sigop'45'out'45'aux_1302
du_pure'45'sigop'45'out'45'aux_1302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'aux_1302
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_3032
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_1304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_1304 ~v0 ~v1
  = du_pure'45'sigop'45'out'45'val_1304
du_pure'45'sigop'45'out'45'val_1304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_1304
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'val_3008
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_1306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_1306 ~v0 ~v1
  = du_pure'45'sigop'45'output_1306
du_pure'45'sigop'45'output_1306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'output_1306
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_3002
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.readReg-typed
d_readReg'45'typed_1308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_1308 ~v0 ~v1 = du_readReg'45'typed_1308
du_readReg'45'typed_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_1308 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2762 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.readTyped
d_readTyped_1310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_readTyped_1310 ~v0 ~v1 = du_readTyped_1310
du_readTyped_1310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_readTyped_1310 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2818 v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.readTyped-cell
d_readTyped'45'cell_1312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readTyped'45'cell_1312 ~v0 ~v1 = du_readTyped'45'cell_1312
du_readTyped'45'cell_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readTyped'45'cell_1312 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'cell_2710 v2
      v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.readTyped-float
d_readTyped'45'float_1314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_readTyped'45'float_1314 ~v0 ~v1 = du_readTyped'45'float_1314
du_readTyped'45'float_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_readTyped'45'float_1314 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'float_2704 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.readTyped-int
d_readTyped'45'int_1316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_readTyped'45'int_1316 ~v0 ~v1 = du_readTyped'45'int_1316
du_readTyped'45'int_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_readTyped'45'int_1316 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'int_2700 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.readTyped-pair
d_readTyped'45'pair_1318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_readTyped'45'pair_1318 ~v0 ~v1 = du_readTyped'45'pair_1318
du_readTyped'45'pair_1318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_1318 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'pair_2746 v3
      v4 v5 v6 v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.readTyped-sum
d_readTyped'45'sum_1320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  (Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readTyped'45'sum_1320 ~v0 ~v1 = du_readTyped'45'sum_1320
du_readTyped'45'sum_1320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  (Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readTyped'45'sum_1320 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'sum_2772 v3 v4
      v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.res-sv
d_res'45'sv_1322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_res'45'sv_1322 ~v0 ~v1 = du_res'45'sv_1322
du_res'45'sv_1322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_res'45'sv_1322 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_res'45'sv_3012 v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.sigop-events
d_sigop'45'events_1324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events_1324 ~v0 ~v1 = du_sigop'45'events_1324
du_sigop'45'events_1324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events_1324 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sigop'45'events_3100 v1 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.sigop-events-of
d_sigop'45'events'45'of_1326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events'45'of_1326 ~v0 ~v1
  = du_sigop'45'events'45'of_1326
du_sigop'45'events'45'of_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events'45'of_1326 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sigop'45'events'45'of_3082
      v1 v3 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_1328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_structured'45'pure'45'sigop'45'output_1328 ~v0 ~v1
  = du_structured'45'pure'45'sigop'45'output_1328
du_structured'45'pure'45'sigop'45'output_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_structured'45'pure'45'sigop'45'output_1328
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2864
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_1330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_unit'45'storedvalue_1330 ~v0 ~v1 = du_unit'45'storedvalue_1330
du_unit'45'storedvalue_1330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_unit'45'storedvalue_1330 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_unit'45'storedvalue_2688
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AllocState.block-size
d_block'45'size_1404 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> Integer
d_block'45'size_1404 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_594 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AllocState.current-frame
d_current'45'frame_1406 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> AgdaAny
d_current'45'frame_1406 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AllocState.frame-slots
d_frame'45'slots_1408 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_frame'45'slots_1408 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_588 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AllocState.next-heap-ref
d_next'45'heap'45'ref_1410 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'heap'45'ref_1410 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AllocState.next-slot
d_next'45'slot_1412 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'slot_1412 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_590 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.AllocState.saved-frames
d_saved'45'frames_1414 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_1414 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_586 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.AllSlotStable
d_AllSlotStable_1418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_AllSlotStable_1418 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.SlotStable
d_SlotStable_1420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_SlotStable_1420 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.SlotStableT
d_SlotStableT_1422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_SlotStableT_1422 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.abstract-keeps-next-slot
d_abstract'45'keeps'45'next'45'slot_1424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abstract'45'keeps'45'next'45'slot_1424 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.case-keeps-next-slot
d_case'45'keeps'45'next'45'slot_1426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'keeps'45'next'45'slot_1426 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.elfs-alloc
d_elfs'45'alloc_1428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elfs'45'alloc_1428 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.eris-alloc
d_eris'45'alloc_1430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eris'45'alloc_1430 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.exec-flat-keeps-next-slot
d_exec'45'flat'45'keeps'45'next'45'slot_1432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'keeps'45'next'45'slot_1432 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.flat-keeps-next-slot
d_flat'45'keeps'45'next'45'slot_1434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'keeps'45'next'45'slot_1434 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.CataNextSlot.trace-keeps-next-slot
d_trace'45'keeps'45'next'45'slot_1436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'keeps'45'next'45'slot_1436 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Decimal.exp10
d_exp10_1440 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_exp10_1440 v0
  = coe MAlonzo.Code.Once.Float.Decimal.d_exp10_14 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.Decimal.sig
d_sig_1442 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_sig_1442 v0
  = coe MAlonzo.Code.Once.Float.Decimal.d_sig_12 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.ChainNotNested
d_ChainNotNested_1462 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 -> ()
d_ChainNotNested_1462 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.NotNested
d_NotNested_1464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_NotNested_1464 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.chain-events
d_chain'45'events_1466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_chain'45'events_1466 ~v0 ~v1 = du_chain'45'events_1466
du_chain'45'events_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_chain'45'events_1466 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_604 v0 v1
      v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.chain-events-++
d_chain'45'events'45''43''43'_1468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_1468 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.chain-events-len0
d_chain'45'events'45'len0_1470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'len0_1470 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.chain-events-nil
d_chain'45'events'45'nil_1472 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_1472 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.chain-events-subst
d_chain'45'events'45'subst_1474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst_1474 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.chain-events-subst-len
d_chain'45'events'45'subst'45'len_1476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'len_1476 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.chain-events-subst-start
d_chain'45'events'45'subst'45'start_1478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_1478 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.chain-log
d_chain'45'log_1480 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'log_1480 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.ev-of-loc
d_ev'45'of'45'loc_1482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_ev'45'of'45'loc_1482 ~v0 ~v1 = du_ev'45'of'45'loc_1482
du_ev'45'of'45'loc_1482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_ev'45'of'45'loc_1482 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_ev'45'of'45'loc_452 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.event-of
d_event'45'of_1484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_event'45'of_1484 ~v0 ~v1 = du_event'45'of_1484
du_event'45'of_1484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_event'45'of_1484 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_458 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.flat-events
d_flat'45'events_1486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'events_1486 ~v0 ~v1 = du_flat'45'events_1486
du_flat'45'events_1486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'events_1486
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_464
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.flat-events-[]
d_flat'45'events'45''91''93'_1488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_1488 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.flat-events-fetch
d_flat'45'events'45'fetch_1490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'events'45'fetch_1490 ~v0 ~v1
  = du_flat'45'events'45'fetch_1490
du_flat'45'events'45'fetch_1490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'events'45'fetch_1490
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'fetch_468
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.flat-events-halted
d_flat'45'events'45'halted_1492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'halted_1492 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.flat-events-reify
d_flat'45'events'45'reify_1494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_876 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'reify_1494 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.flat-events-settled
d_flat'45'events'45'settled_1496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'settled_1496 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.flat-events-step
d_flat'45'events'45'step_1498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'events'45'step_1498 ~v0 ~v1
  = du_flat'45'events'45'step_1498
du_flat'45'events'45'step_1498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'events'45'step_1498
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'step_466
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.flat-events-steps
d_flat'45'events'45'steps_1500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'steps_1500 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatEventTrace.step-log
d_step'45'log_1502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'log_1502 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.CallPost
d_CallPost_1506 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.FlatState
d_FlatState_1508 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.FlinkView
d_FlinkView_1512 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ProgFree
d_ProgFree_1514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_ProgFree_1514 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.Shifted
d_Shifted_1516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Shifted_1516 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.Straight
d_Straight_1518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_Straight_1518 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.StraightStep
d_StraightStep_1520 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_StraightStep_1520 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.callView
d_callView_1522 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350
d_callView_1522 ~v0 ~v1 = du_callView_1522
du_callView_1522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350
du_callView_1522
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1368
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-branch
d_do'45'branch_1528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_1528 ~v0 ~v1 = du_do'45'branch_1528
du_do'45'branch_1528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch_1528
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_938
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-branch-at
d_do'45'branch'45'at_1530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch'45'at_1530 ~v0 ~v1 = du_do'45'branch'45'at_1530
du_do'45'branch'45'at_1530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch'45'at_1530 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'branch'45'at_930 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-call
d_do'45'call_1532 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_1532 ~v0 ~v1 = du_do'45'call_1532
du_do'45'call_1532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call_1532
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-call-at
d_do'45'call'45'at_1534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_1534 ~v0 ~v1 = du_do'45'call'45'at_1534
du_do'45'call'45'at_1534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'at_1534
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1284
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-call-code
d_do'45'call'45'code_1536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'code_1536 ~v0 ~v1 = du_do'45'call'45'code_1536
du_do'45'call'45'code_1536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'code_1536
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'code_1292
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-call-code-prefix
d_do'45'call'45'code'45'prefix_1538 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'code'45'prefix_1538 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-call-prefix
d_do'45'call'45'prefix_1540 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'prefix_1540 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-call-sv
d_do'45'call'45'sv_1542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'sv_1542 ~v0 ~v1 = du_do'45'call'45'sv_1542
du_do'45'call'45'sv_1542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'sv_1542
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'sv_1316
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-call-sv-prefix
d_do'45'call'45'sv'45'prefix_1544 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'sv'45'prefix_1544 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-jump
d_do'45'jump_1546 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_1546 ~v0 ~v1 = du_do'45'jump_1546
du_do'45'jump_1546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_1546 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_922 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-ret
d_do'45'ret_1548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_1548 ~v0 ~v1 = du_do'45'ret_1548
du_do'45'ret_1548 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_1548 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_1140 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-ret-alloc
d_do'45'ret'45'alloc_1550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_1550 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_1552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_1552 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_1554 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_1554 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_1556 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_1556 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_1558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_1558 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-save-closure
d_do'45'save'45'closure_1560 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'save'45'closure_1560 ~v0 ~v1
  = du_do'45'save'45'closure_1560
du_do'45'save'45'closure_1560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'save'45'closure_1560 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1498 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.do-thunk
d_do'45'thunk_1562 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_1562 ~v0 ~v1 = du_do'45'thunk_1562
du_do'45'thunk_1562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_1562
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1274
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.enter-call
d_enter'45'call_1564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_enter'45'call_1564 ~v0 ~v1 = du_enter'45'call_1564
du_enter'45'call_1564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_enter'45'call_1564
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.enter-frame
d_enter'45'frame_1566 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_enter'45'frame_1566 ~v0 ~v1 = du_enter'45'frame_1566
du_enter'45'frame_1566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_enter'45'frame_1566
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'frame_954
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.entry-of?
d_entry'45'of'63'_1568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
d_entry'45'of'63'_1568 ~v0 ~v1 = du_entry'45'of'63'_1568
du_entry'45'of'63'_1568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
du_entry'45'of'63'_1568 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63'_168 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.entry-of?-sound
d_entry'45'of'63''45'sound_1570 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'of'63''45'sound_1570 ~v0 ~v1
  = du_entry'45'of'63''45'sound_1570
du_entry'45'of'63''45'sound_1570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'of'63''45'sound_1570 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63''45'sound_634
      v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.entry→thunk
d_entry'8594'thunk_1572 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8594'thunk_1572 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.exec-flat
d_exec'45'flat_1574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_1574 ~v0 ~v1 = du_exec'45'flat_1574
du_exec'45'flat_1574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_exec'45'flat_1574
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3630
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.exec-flat-halted
d_exec'45'flat'45'halted_1576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_1576 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.exec-flat-invariant
d_exec'45'flat'45'invariant_1578 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_1578 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.exec-flat-offend
d_exec'45'flat'45'offend_1580 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_1580 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.exec-flat-reloc
d_exec'45'flat'45'reloc_1582 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'flat'45'reloc_1582 ~v0 ~v1
  = du_exec'45'flat'45'reloc_1582
du_exec'45'flat'45'reloc_1582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'flat'45'reloc_1582 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'flat'45'reloc_3680 v0
      v1 v2 v3 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.exec-flat-step
d_exec'45'flat'45'step_1584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_1584 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_1586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_1586 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.exec-trace-halted
d_exec'45'trace'45'halted_1588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_1588 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_1590 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_1590 ~v0 ~v1
  = du_exec'45'trace'45'is'45'flat_1590
du_exec'45'trace'45'is'45'flat_1590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_1590 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'trace'45'is'45'flat_4456
      v1 v2 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.falloc
d_falloc_1592 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_1592 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fclosure
d_fclosure_1594 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1594 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fetch
d_fetch_1596 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_fetch_1596 ~v0 ~v1 = du_fetch_1596
du_fetch_1596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
du_fetch_1596 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fetch-++-left
d_fetch'45''43''43''45'left_1598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'left_1598 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fetch-++-right
d_fetch'45''43''43''45'right_1600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'right_1600 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fetch-All
d_fetch'45'All_1602 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_1602 ~v0 ~v1 = du_fetch'45'All_1602
du_fetch'45'All_1602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_fetch'45'All_1602 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_4132 v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fetch-Straight
d_fetch'45'Straight_1604 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_1604 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fetch-dispatch
d_fetch'45'dispatch_1606 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fetch'45'dispatch_1606 ~v0 ~v1 = du_fetch'45'dispatch_1606
du_fetch'45'dispatch_1606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fetch'45'dispatch_1606
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fetch'45'dispatch_3634
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.find-entry
d_find'45'entry_1608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Maybe Integer
d_find'45'entry_1608 ~v0 ~v1 = du_find'45'entry_1608
du_find'45'entry_1608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Maybe Integer
du_find'45'entry_1608
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'entry_228
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.find-entry-sound
d_find'45'entry'45'sound_1610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'entry'45'sound_1610 ~v0 ~v1
  = du_find'45'entry'45'sound_1610
du_find'45'entry'45'sound_1610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'entry'45'sound_1610 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'entry'45'sound_882 v0
      v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.find-fn
d_find'45'fn_1612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Maybe Integer
d_find'45'fn_1612 ~v0 ~v1 = du_find'45'fn_1612
du_find'45'fn_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Maybe Integer
du_find'45'fn_1612
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.find-label
d_find'45'label_1614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_1614 ~v0 ~v1 = du_find'45'label_1614
du_find'45'label_1614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_1614
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.find-label-lands
d_find'45'label'45'lands_1616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_1616 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.find-label-sound
d_find'45'label'45'sound_1618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_1618 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.find-thunk
d_find'45'thunk_1620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_1620 ~v0 ~v1 = du_find'45'thunk_1620
du_find'45'thunk_1620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_1620
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.find-thunk-sound
d_find'45'thunk'45'sound_1622 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_1622 ~v0 ~v1
  = du_find'45'thunk'45'sound_1622
du_find'45'thunk'45'sound_1622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'sound_1622
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk'45'sound_916
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fl-at
d_fl'45'at_1624 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_1624 ~v0 ~v1 = du_fl'45'at_1624
du_fl'45'at_1624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'at_1624
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'at_128
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fl-at-++-miss
d_fl'45'at'45''43''43''45'miss_1626 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'at'45''43''43''45'miss_1626 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fl-go
d_fl'45'go_1628 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_1628 ~v0 ~v1 = du_fl'45'go_1628
du_fl'45'go_1628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'go_1628
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fl-go-++-miss
d_fl'45'go'45''43''43''45'miss_1630 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45''43''43''45'miss_1630 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fl-go-lands
d_fl'45'go'45'lands_1632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_1632 ~v0 ~v1 = du_fl'45'go'45'lands_1632
du_fl'45'go'45'lands_1632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_1632 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'lands_3916 v0 v1
      v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fl-go-sound
d_fl'45'go'45'sound_1634 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_1634 ~v0 ~v1 = du_fl'45'go'45'sound_1634
du_fl'45'go'45'sound_1634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_1634 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'sound_762 v0 v1
      v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fl-label-match
d_fl'45'label'45'match_1636 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_1636 ~v0 ~v1 = du_fl'45'label'45'match_1636
du_fl'45'label'45'match_1636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'label'45'match_1636
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fl-match-++-miss
d_fl'45'match'45''43''43''45'miss_1638 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'match'45''43''43''45'miss_1638 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flat-exec-instr
d_flat'45'exec'45'instr_1640 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_1640 ~v0 ~v1
  = du_flat'45'exec'45'instr_1640
du_flat'45'exec'45'instr_1640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_1640
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flat-exec-instr-prefix
d_flat'45'exec'45'instr'45'prefix_1642 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prefix_1642 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flat-exec-instr-prog-irrelevant
d_flat'45'exec'45'instr'45'prog'45'irrelevant_1644 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prog'45'irrelevant_1644 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flat-halt
d_flat'45'halt_1646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'halt_1646 ~v0 ~v1 = du_flat'45'halt_1646
du_flat'45'halt_1646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'halt_1646 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'halt_1280 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flat-read-at
d_flat'45'read'45'at_1648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'at_1648 ~v0 ~v1 = du_flat'45'read'45'at_1648
du_flat'45'read'45'at_1648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'at_1648 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'at_110 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flat-read-tag
d_flat'45'read'45'tag_1650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_1650 ~v0 ~v1 = du_flat'45'read'45'tag_1650
du_flat'45'read'45'tag_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_1650 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flat-step-frame
d_flat'45'step'45'frame_1652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'frame_1652 ~v0 ~v1
  = du_flat'45'step'45'frame_1652
du_flat'45'step'45'frame_1652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'frame_1652
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'frame_1132
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flat-step-straight
d_flat'45'step'45'straight_1654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'straight_1654 ~v0 ~v1
  = du_flat'45'step'45'straight_1654
du_flat'45'step'45'straight_1654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'straight_1654
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flink
d_flink_1656 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1656 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flink-do-branch
d_flink'45'do'45'branch_1658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch_1658 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flink-do-jump
d_flink'45'do'45'jump_1660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'jump_1660 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flink-do-ret
d_flink'45'do'45'ret_1662 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'ret_1662 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.flinkView
d_flinkView_1664 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3448
d_flinkView_1664 ~v0 ~v1 = du_flinkView_1664
du_flinkView_1664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3448
du_flinkView_1664 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flinkView_3476 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.floc
d_floc_1666 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_1666 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.forced
d_forced_1668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_forced_1668 ~v0 ~v1 = du_forced_1668
du_forced_1668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_forced_1668 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_4446 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fpc
d_fpc_1670 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1670 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.fret
d_fret_1672 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1672 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-at
d_ft'45'at_1674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'at_1674 ~v0 ~v1 = du_ft'45'at_1674
du_ft'45'at_1674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'at_1674
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'at_194
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-at-++-miss
d_ft'45'at'45''43''43''45'miss_1676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45''43''43''45'miss_1676 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-at-prefix
d_ft'45'at'45'prefix_1678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45'prefix_1678 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-go
d_ft'45'go_1680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'go_1680 ~v0 ~v1 = du_ft'45'go_1680
du_ft'45'go_1680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'go_1680
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_192
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-go-++-miss
d_ft'45'go'45''43''43''45'miss_1682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45''43''43''45'miss_1682 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-go-prefix
d_ft'45'go'45'prefix_1684 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45'prefix_1684 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-go-sound
d_ft'45'go'45'sound_1686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_1686 ~v0 ~v1 = du_ft'45'go'45'sound_1686
du_ft'45'go'45'sound_1686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_1686 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_ft'45'go'45'sound_654 v0 v1
      v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-match
d_ft'45'match_1688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'match_1688 ~v0 ~v1 = du_ft'45'match_1688
du_ft'45'match_1688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'match_1688
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_196
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-match-++-miss
d_ft'45'match'45''43''43''45'miss_1690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45''43''43''45'miss_1690 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.ft-match-prefix
d_ft'45'match'45'prefix_1692 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45'prefix_1692 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.grow-frame
d_grow'45'frame_1704 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_grow'45'frame_1704 ~v0 ~v1 = du_grow'45'frame_1704
du_grow'45'frame_1704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_grow'45'frame_1704
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_grow'45'frame_1268
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.just-injℕ
d_just'45'injℕ_1706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_1706 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.lab-eq
d_lab'45'eq_1708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_1708 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.label-of?
d_label'45'of'63'_1710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_1710 ~v0 ~v1 = du_label'45'of'63'_1710
du_label'45'of'63'_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_1710 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_122 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.label-of?-sound
d_label'45'of'63''45'sound_1712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_1712 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.leave-frame
d_leave'45'frame_1714 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_leave'45'frame_1714 ~v0 ~v1 = du_leave'45'frame_1714
du_leave'45'frame_1714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_leave'45'frame_1714 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_976 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.leave-frame-aux
d_leave'45'frame'45'aux_1716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_leave'45'frame'45'aux_1716 ~v0 ~v1
  = du_leave'45'frame'45'aux_1716
du_leave'45'frame'45'aux_1716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_leave'45'frame'45'aux_1716 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_964 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.leave-frame-block-size
d_leave'45'frame'45'block'45'size_1718 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_1718 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_1720 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_1720 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_1722 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_1722 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_1724 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_1724 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_1726 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_1726 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_1728 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_1728 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_1730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_1730 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.mkFlat
d_mkFlat_1732 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_mkFlat_1732 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v0)
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.reloc-fetch
d_reloc'45'fetch_1736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'fetch_1736 ~v0 ~v1 = du_reloc'45'fetch_1736
du_reloc'45'fetch_1736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'fetch_1736 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'fetch_3724 v0 v1 v2
      v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.reloc-step
d_reloc'45'step_1738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'step_1738 ~v0 ~v1 = du_reloc'45'step_1738
du_reloc'45'step_1738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'step_1738 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'step_3702 v0 v1 v2
      v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shift
d_shift_1740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_shift_1740 ~v0 ~v1 = du_shift_1740
du_shift_1740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_shift_1740 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shift_3374 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shift-loc
d_shift'45'loc_1742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_1742 ~v0 ~v1 = du_shift'45'loc_1742
du_shift'45'loc_1742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_1742 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shift'45'loc_4298 v0 v1 v3 v4
      v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-branch
d_shifted'45'branch_1744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'branch_1744 ~v0 ~v1 = du_shifted'45'branch_1744
du_shifted'45'branch_1744 ::
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
du_shifted'45'branch_1744 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'branch_1824 v2 v5
      v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-call-at
d_shifted'45'call'45'at_1746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'call'45'at_1746 ~v0 ~v1
  = du_shifted'45'call'45'at_1746
du_shifted'45'call'45'at_1746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'at_1746 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'at_1962 v3
      v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-call-closure
d_shifted'45'call'45'closure_1748 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'closure_1748 ~v0 ~v1
  = du_shifted'45'call'45'closure_1748
du_shifted'45'call'45'closure_1748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'closure_1748 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'closure_2178
      v0 v3 v4 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-call-code
d_shifted'45'call'45'code_1750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'code_1750 ~v0 ~v1
  = du_shifted'45'call'45'code_1750
du_shifted'45'call'45'code_1750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'code_1750 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'code_2010
      v0 v2 v4 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-call-sv
d_shifted'45'call'45'sv_1752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'sv_1752 ~v0 ~v1
  = du_shifted'45'call'45'sv_1752
du_shifted'45'call'45'sv_1752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'sv_1752 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'sv_2092 v0
      v2 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-eq
d_shifted'45'eq_1754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shifted'45'eq_1754 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-frame
d_shifted'45'frame_1756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'frame_1756 ~v0 ~v1 = du_shifted'45'frame_1756
du_shifted'45'frame_1756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'frame_1756 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'frame_1862 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-halt
d_shifted'45'halt_1758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'halt_1758 ~v0 ~v1 = du_shifted'45'halt_1758
du_shifted'45'halt_1758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'halt_1758 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'halt_1928 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-instr
d_shifted'45'instr_1760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'instr_1760 ~v0 ~v1 = du_shifted'45'instr_1760
du_shifted'45'instr_1760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'instr_1760 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'instr_2218 v0 v2
      v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-jump
d_shifted'45'jump_1762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'jump_1762 ~v0 ~v1 = du_shifted'45'jump_1762
du_shifted'45'jump_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'jump_1762 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'jump_1766 v3 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-label
d_shifted'45'label_1764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'label_1764 ~v0 ~v1 = du_shifted'45'label_1764
du_shifted'45'label_1764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'label_1764 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'label_1624 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-ret
d_shifted'45'ret_1766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret_1766 ~v0 ~v1 = du_shifted'45'ret_1766
du_shifted'45'ret_1766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret_1766 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret_1742 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-ret-aux
d_shifted'45'ret'45'aux_1768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'ret'45'aux_1768 ~v0 ~v1
  = du_shifted'45'ret'45'aux_1768
du_shifted'45'ret'45'aux_1768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret'45'aux_1768 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret'45'aux_1690 v3
      v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-save-closure
d_shifted'45'save'45'closure_1770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'save'45'closure_1770 ~v0 ~v1
  = du_shifted'45'save'45'closure_1770
du_shifted'45'save'45'closure_1770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'save'45'closure_1770 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'save'45'closure_1900
      v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-shift
d_shifted'45'shift_1772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'shift_1772 ~v0 ~v1 = du_shifted'45'shift_1772
du_shifted'45'shift_1772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'shift_1772 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'shift_3388
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-straight
d_shifted'45'straight_1774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'straight_1774 ~v0 ~v1 = du_shifted'45'straight_1774
du_shifted'45'straight_1774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'straight_1774 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'straight_1588 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.shifted-thunk
d_shifted'45'thunk_1776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'thunk_1776 ~v0 ~v1 = du_shifted'45'thunk_1776
du_shifted'45'thunk_1776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'thunk_1776 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'thunk_1652 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.step-dispatch
d_step'45'dispatch_1778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_step'45'dispatch_1778 ~v0 ~v1 = du_step'45'dispatch_1778
du_step'45'dispatch_1778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_step'45'dispatch_1778
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_step'45'dispatch_3632
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.sv-is-zero
d_sv'45'is'45'zero_1780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_1780 ~v0 ~v1 = du_sv'45'is'45'zero_1780
du_sv'45'is'45'zero_1780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_1780 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.tag-zf
d_tag'45'zf_1782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_1782 ~v0 ~v1 = du_tag'45'zf_1782
du_tag'45'zf_1782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_1782 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.thunk-of?
d_thunk'45'of'63'_1784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_1784 ~v0 ~v1 = du_thunk'45'of'63'_1784
du_thunk'45'of'63'_1784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_1784 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63'_176 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.thunk-of?-sound
d_thunk'45'of'63''45'sound_1786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_1786 ~v0 ~v1
  = du_thunk'45'of'63''45'sound_1786
du_thunk'45'of'63''45'sound_1786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_1786 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63''45'sound_620
      v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.thunk-part
d_thunk'45'part_1788 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'part_1788 ~v0 ~v1 = du_thunk'45'part_1788
du_thunk'45'part_1788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'part_1788 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'part_172 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.≡ᵇ-true
d_'8801''7495''45'true_1790 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_1790 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.FlatState.falloc
d_falloc_1800 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_1800 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.FlatState.fclosure
d_fclosure_1802 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1802 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.FlatState.flink
d_flink_1804 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1804 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.FlatState.floc
d_floc_1806 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_1806 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.FlatState.fpc
d_fpc_1808 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1808 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatMachine.FlatState.fret
d_fret_1810 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1810 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.FlatSteps
d_FlatSteps_1828 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.FlatSteps-++
d_FlatSteps'45''43''43'_1830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_FlatSteps'45''43''43'_1830 ~v0 ~v1
  = du_FlatSteps'45''43''43'_1830
du_FlatSteps'45''43''43'_1830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_FlatSteps'45''43''43'_1830 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1192
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.FlatSteps-middle
d_FlatSteps'45'middle_1832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_FlatSteps'45'middle_1832 ~v0 ~v1 = du_FlatSteps'45'middle_1832
du_FlatSteps'45'middle_1832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_FlatSteps'45'middle_1832 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'middle_1112
      v9
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.FlatSteps-prefix
d_FlatSteps'45'prefix_1834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_FlatSteps'45'prefix_1834 ~v0 ~v1 = du_FlatSteps'45'prefix_1834
du_FlatSteps'45'prefix_1834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_FlatSteps'45'prefix_1834 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'prefix_1020
      v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.FlatSteps-reloc
d_FlatSteps'45'reloc_1836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_FlatSteps'45'reloc_1836 ~v0 ~v1 = du_FlatSteps'45'reloc_1836
du_FlatSteps'45'reloc_1836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_FlatSteps'45'reloc_1836 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'reloc_1062
      v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.RunReified
d_RunReified_1838 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.chain-steps
d_chain'45'steps_1844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_chain'45'steps_1844 ~v0 ~v1 = du_chain'45'steps_1844
du_chain'45'steps_1844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_chain'45'steps_1844 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_chain'45'steps_1212
      v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.chain-steps-nil
d_chain'45'steps'45'nil_1846 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'steps'45'nil_1846 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.exec-flat-steps
d_exec'45'flat'45'steps_1848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_1848 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.fetch-++
d_fetch'45''43''43'_1850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43'_1850 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.find-label-distrib
d_find'45'label'45'distrib_1852 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'distrib_1852 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.fl-go-prefix
d_fl'45'go'45'prefix_1854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'prefix_1854 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.fl-go-shift
d_fl'45'go'45'shift_1856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'shift_1856 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.fl-go-skip
d_fl'45'go'45'skip_1858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'skip_1858 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.flat-jmp
d_flat'45'jmp_1860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'jmp_1860 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.flat-label
d_flat'45'label_1862 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'label_1862 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.flat-scratch-branch-not
d_flat'45'scratch'45'branch'45'not_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'not_1864 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.flat-scratch-branch-yes
d_flat'45'scratch'45'branch'45'yes_1866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'yes_1866 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.flat-step1
d_flat'45'step1_1868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_flat'45'step1_1868 ~v0 ~v1 = du_flat'45'step1_1868
du_flat'45'step1_1868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_flat'45'step1_1868 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_flat'45'step1_436
      v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.flat-tag-branch-not
d_flat'45'tag'45'branch'45'not_1870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'not_1870 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.flat-tag-branch-yes
d_flat'45'tag'45'branch'45'yes_1872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'yes_1872 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.flm-prefix
d_flm'45'prefix_1874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'prefix_1874 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.flm-shift
d_flm'45'shift_1876 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'shift_1876 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.link-block-steps
d_link'45'block'45'steps_1878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2314 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_link'45'block'45'steps_1878 ~v0 ~v1
  = du_link'45'block'45'steps_1878
du_link'45'block'45'steps_1878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2314 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_link'45'block'45'steps_1878 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_link'45'block'45'steps_1156
      v13
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.reify-run
d_reify'45'run_1882 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_876
d_reify'45'run_1882 ~v0 ~v1 = du_reify'45'run_1882
du_reify'45'run_1882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_876
du_reify'45'run_1882
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_reify'45'run_916
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.step-at
d_step'45'at_1884 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_step'45'at_1884 ~v0 ~v1 = du_step'45'at_1884
du_step'45'at_1884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_step'45'at_1884 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_388 v5
      v7 v9
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.RunReified.chain
d_chain_1894 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_876 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_chain_1894 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_chain_902 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.RunReified.fuel-split
d_fuel'45'split_1896 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_876 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_1896 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.RunReified.rest-fuel
d_rest'45'fuel_1898 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_876 ->
  Integer
d_rest'45'fuel_1898 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_rest'45'fuel_898
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.RunReified.settle
d_settle_1900 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_876 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1900 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settle_900 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.RunReified.settled
d_settled_1902 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_876 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_1902 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settled_904 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FlatStepsAPI.RunReified.steps-len
d_steps'45'len_1904 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_876 ->
  Integer
d_steps'45'len_1904 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_steps'45'len_896
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics._≟F_
d__'8799'F__1906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__1906 v0
  = coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics._≺_
d__'8826'__1908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> ()
d__'8826'__1908 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.Frame
d_Frame_1910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_Frame_1910 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.float-format
d_float'45'format_1912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_1912 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.frame-base
d_frame'45'base_1914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
d_frame'45'base_1914 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_1916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_1916 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.frame-word
d_frame'45'word_1918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_frame'45'word_1918 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_110 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_1920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_1920 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word'45'pos_112
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.fs-interp
d_fs'45'interp_1922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_fs'45'interp_1922 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.shift-base
d_shift'45'base_1924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_1924 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.shift-frame
d_shift'45'frame_1926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_1926 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_108 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.slot-addr
d_slot'45'addr_1928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_1928 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_94 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_1930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_1930 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.slot-injective
d_slot'45'injective_1932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_1932 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_1934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_1934 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.≺-compare
d_'8826''45'compare_1936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_1936 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'compare_148
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_1938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_1938 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrameSemantics.≺-trans
d_'8826''45'trans_1940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_1940 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_138 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.AllocBump
d_AllocBump_1944 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.BeforeFrontier
d_BeforeFrontier_1948 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.StackAncestorSource
d_StackAncestorSource_1950 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.apply-bump
d_apply'45'bump_1952 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_apply'45'bump_1952 ~v0 ~v1 = du_apply'45'bump_1952
du_apply'45'bump_1952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_apply'45'bump_1952 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_942 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_1954 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_1954 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.apply-bump-compose
d_apply'45'bump'45'compose_1956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_1956 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_1958 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_1958 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_1960 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_1960 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.bump-+
d_bump'45''43'_1962 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump'45''43'_1962 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_mkBump_940
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_936
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_936
            (coe v1)))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_938
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_938
            (coe v1)))
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.bump-0
d_bump'45'0_1964 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump'45'0_1964 ~v0 ~v1 = du_bump'45'0_1964
du_bump'45'0_1964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
du_bump'45'0_1964 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Allocation.du_bump'45'0_948
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.fresh-stack-after
d_fresh'45'stack'45'after_1966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_1966 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.frontier-monotone
d_frontier'45'monotone_1968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_frontier'45'monotone_1968 ~v0 ~v1 = du_frontier'45'monotone_1968
du_frontier'45'monotone_1968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_frontier'45'monotone_1968 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.heap-alloc-advances
d_heap'45'alloc'45'advances_1970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_heap'45'alloc'45'advances_1970 ~v0 ~v1
  = du_heap'45'alloc'45'advances_1970
du_heap'45'alloc'45'advances_1970 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_heap'45'alloc'45'advances_1970 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_heap'45'alloc'45'advances_834
      v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1976 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 -> Integer
d_next'45'heap'45'ref'45'delta_1976 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_938
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.next-slot-delta
d_next'45'slot'45'delta_1978 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 -> Integer
d_next'45'slot'45'delta_1978 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_936
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.stack-alloc-advances
d_stack'45'alloc'45'advances_1984 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_stack'45'alloc'45'advances_1984 ~v0 ~v1
  = du_stack'45'alloc'45'advances_1984
du_stack'45'alloc'45'advances_1984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_stack'45'alloc'45'advances_1984 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
      v1 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.≺⇒≢
d_'8826''8658''8802'_1990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_1990 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1994 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 -> Integer
d_next'45'heap'45'ref'45'delta_1994 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_938
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.FrontierInvariant.AllocBump.next-slot-delta
d_next'45'slot'45'delta_1996 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 -> Integer
d_next'45'slot'45'delta_1996 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_936
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.HeapLocation.heap-offset
d_heap'45'offset_2012 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_heap'45'offset_2012 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.HeapLocation.heap-ref
d_heap'45'ref_2014 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
d_heap'45'ref_2014 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.HeapRef.ref-id
d_ref'45'id_2016 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 -> Integer
d_ref'45'id_2016 v0
  = coe MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.LocState-eq
d_LocState'45'eq_2080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_LocState'45'eq_2080 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.REFUTABLE-effect-state-only-frame-dep
d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2082 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny
d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2082 ~v0 ~v1
  = du_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2082
du_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny
du_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2082
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2910
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.case-on-tag-state-next-slot-invariant
d_case'45'on'45'tag'45'state'45'next'45'slot'45'invariant_2084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'on'45'tag'45'state'45'next'45'slot'45'invariant_2084
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.exec-abstract-deterministic
d_exec'45'abstract'45'deterministic_2086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'deterministic_2086 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_2088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_2088 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_2090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_2090 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_2092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_2092 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.exec-abstract-same-frame
d_exec'45'abstract'45'same'45'frame_2094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'same'45'frame_2094 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.exec-abstract-state-next-slot-invariant
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_2096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_2096
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.exec-case-dispatch-preserves-frame
d_exec'45'case'45'dispatch'45'preserves'45'frame_2098 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'case'45'dispatch'45'preserves'45'frame_2098 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.exec-loop-preserves-frame
d_exec'45'loop'45'preserves'45'frame_2100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'loop'45'preserves'45'frame_2100 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.exec-trace-preserves-frame
d_exec'45'trace'45'preserves'45'frame_2102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'frame_2102 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.loop-state-next-slot-invariant
d_loop'45'state'45'next'45'slot'45'invariant_2104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loop'45'state'45'next'45'slot'45'invariant_2104 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.next-slot-update-preserves-frame
d_next'45'slot'45'update'45'preserves'45'frame_2106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'frame_2106 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.next-slot-update-preserves-heap-ref
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_2108 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_2108 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.store-at-slot-preserves-above
d_store'45'at'45'slot'45'preserves'45'above_2110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'above_2110 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_2112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_2112 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_2114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_2114 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.InstrPrimitives.worklist-push-preserves-stack-slot
d_worklist'45'push'45'preserves'45'stack'45'slot_2116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_worklist'45'push'45'preserves'45'stack'45'slot_2116 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LabelId.idx
d_idx_2120 :: MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_idx_2120 v0 = coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LabelId.owner
d_owner_2122 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_owner_2122 v0
  = coe MAlonzo.Code.Once.CCC.Label.d_owner_14 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LabelId.path
d_path_2124 :: MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> [Integer]
d_path_2124 v0 = coe MAlonzo.Code.Once.CCC.Label.d_path_16 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LocState.ev-log
d_ev'45'log_2130 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_ev'45'log_2130 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LocState.halted
d_halted_2132 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_halted_2132 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_422 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LocState.heapMem
d_heapMem_2134 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_heapMem_2134 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_420 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LocState.regs
d_regs_2136 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs_2136 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.LocState.stackMem
d_stackMem_2138 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_stackMem_2138 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_418 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.clear-frame
d_clear'45'frame_2146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_clear'45'frame_2146 ~v0 ~v1 = du_clear'45'frame_2146
du_clear'45'frame_2146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_clear'45'frame_2146
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_clear'45'frame_710
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.clear-frame-aux
d_clear'45'frame'45'aux_2148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_clear'45'frame'45'aux_2148 ~v0 ~v1
  = du_clear'45'frame'45'aux_2148
du_clear'45'frame'45'aux_2148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_clear'45'frame'45'aux_2148 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_clear'45'frame'45'aux_704
      v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.clear-frame-just
d_clear'45'frame'45'just_2150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_2150 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.readHeapLoc
d_readHeapLoc_2152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readHeapLoc_2152 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_420 v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.readLoc
d_readLoc_2154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_2154 ~v0 ~v1 = du_readLoc_2154
du_readLoc_2154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_2154 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.readStackLoc
d_readStackLoc_2156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readStackLoc_2156 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_418 v0 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeHeapMem
d_writeHeapMem_2158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem_2158 ~v0 ~v1 = du_writeHeapMem_2158
du_writeHeapMem_2158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem_2158 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_792 v1 v2 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_2160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem'45'aux_2160 ~v0 ~v1 = du_writeHeapMem'45'aux_2160
du_writeHeapMem'45'aux_2160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem'45'aux_2160 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_786 v3
      v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLoc
d_writeLoc_2162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_2162 ~v0 ~v1 = du_writeLoc_2162
du_writeLoc_2162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLoc_2162
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_820
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLoc-halted
d_writeLoc'45'halted_2164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2164 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2166 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2168 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2170 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2172 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLoc-regs
d_writeLoc'45'regs_2174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2174 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2176 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2176 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLocToHeap
d_writeLocToHeap_2178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToHeap_2178 ~v0 ~v1 = du_writeLocToHeap_2178
du_writeLocToHeap_2178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToHeap_2178 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_812 v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeLocToStack
d_writeLocToStack_2180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToStack_2180 ~v0 ~v1 = du_writeLocToStack_2180
du_writeLocToStack_2180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToStack_2180
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_802
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeStackMem
d_writeStackMem_2182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeStackMem_2182 ~v0 ~v1 = du_writeStackMem_2182
du_writeStackMem_2182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeStackMem_2182
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeStackMem_682
-- Once.CCC.Codegen.IRObsCorrect.Interface._.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_2184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeStackMem'45'aux_2184 ~v0 ~v1 = du_writeStackMem'45'aux_2184
du_writeStackMem'45'aux_2184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeStackMem'45'aux_2184 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_674 v5
      v6 v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface._.ReadLocEq.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_2188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_2188 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.REFUTABLE-alloc-heap-trace-preserves-heap-ref
d_REFUTABLE'45'alloc'45'heap'45'trace'45'preserves'45'heap'45'ref_2192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_REFUTABLE'45'alloc'45'heap'45'trace'45'preserves'45'heap'45'ref_2192
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.case-on-tag-trace-preserves-heap-ref
d_case'45'on'45'tag'45'trace'45'preserves'45'heap'45'ref_2194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'on'45'tag'45'trace'45'preserves'45'heap'45'ref_2194
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-instr-load-tag-lit-preserves-alloc
d_exec'45'abstract'45'instr'45'load'45'tag'45'lit'45'preserves'45'alloc_2196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'instr'45'load'45'tag'45'lit'45'preserves'45'alloc_2196
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-from-slot-output
d_exec'45'abstract'45'load'45'from'45'slot'45'output_2198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'from'45'slot'45'output_2198 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-from-slot-preserves-alloc
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'alloc_2200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'alloc_2200
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-from-slot-preserves-mem
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'mem_2202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'mem_2202
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-output
d_exec'45'abstract'45'load'45'indirect'45'output_2204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'output_2204 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-alloc
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'alloc_2206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'alloc_2206
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-heapMem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'heapMem_2208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'heapMem_2208
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-input
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'input_2210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'input_2210
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_2212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_2212
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-stackMem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'stackMem_2214 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'stackMem_2214
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-suc-output
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_2216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_2216
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-alloc
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'alloc_2218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'alloc_2218
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-heapMem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'heapMem_2220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'heapMem_2220
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-input
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'input_2222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'input_2222
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_2224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_2224
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-stackMem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'stackMem_2226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'stackMem_2226
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-mov-to-input-input
d_exec'45'abstract'45'mov'45'to'45'input'45'input_2228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'input_2228 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-alloc
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'alloc_2230 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'alloc_2230
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-heapMem
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'heapMem_2232 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'heapMem_2232
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-mem
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'mem_2234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'mem_2234
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-stackMem
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'stackMem_2236 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'stackMem_2236
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-mov-to-output-preserves-alloc
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'alloc_2238 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'alloc_2238
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-mov-to-output-preserves-mem
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'mem_2240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'mem_2240
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-preserves-heap-ref
d_exec'45'abstract'45'preserves'45'heap'45'ref_2242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heap'45'ref_2242 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-restore-input-preserves-alloc
d_exec'45'abstract'45'restore'45'input'45'preserves'45'alloc_2244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'preserves'45'alloc_2244
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-restore-input-preserves-heapMem
d_exec'45'abstract'45'restore'45'input'45'preserves'45'heapMem_2246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'preserves'45'heapMem_2246
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-restore-input-preserves-stackMem
d_exec'45'abstract'45'restore'45'input'45'preserves'45'stackMem_2248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'preserves'45'stackMem_2248
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-restore-input-sets-input
d_exec'45'abstract'45'restore'45'input'45'sets'45'input_2250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'sets'45'input_2250
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-store-at-slot-preserves-alloc
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'alloc_2252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'alloc_2252
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-store-indirect-preserves-alloc
d_exec'45'abstract'45'store'45'indirect'45'preserves'45'alloc_2254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'indirect'45'preserves'45'alloc_2254
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-abstract-store-indirect-suc-preserves-alloc
d_exec'45'abstract'45'store'45'indirect'45'suc'45'preserves'45'alloc_2256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'indirect'45'suc'45'preserves'45'alloc_2256
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.exec-trace-preserves-heap-ref
d_exec'45'trace'45'preserves'45'heap'45'ref_2258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heap'45'ref_2258 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.load-indirect-halted-success
d_load'45'indirect'45'halted'45'success_2260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'indirect'45'halted'45'success_2260 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.load-indirect-suc-halted-success
d_load'45'indirect'45'suc'45'halted'45'success_2262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'indirect'45'suc'45'halted'45'success_2262 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.loop-trace-preserves-heap-ref
d_loop'45'trace'45'preserves'45'heap'45'ref_2264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loop'45'trace'45'preserves'45'heap'45'ref_2264 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.passthrough-mem-preserved
d_passthrough'45'mem'45'preserved_2266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_passthrough'45'mem'45'preserved_2266 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.passthrough-output-is-input
d_passthrough'45'output'45'is'45'input_2268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_passthrough'45'output'45'is'45'input_2268 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.passthrough-preserves-halted
d_passthrough'45'preserves'45'halted_2270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_passthrough'45'preserves'45'halted_2270 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-left-setup-alloc-helper
d_prod'45'left'45'setup'45'alloc'45'helper_2272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'alloc'45'helper_2272 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-left-setup-halted-helper
d_prod'45'left'45'setup'45'halted'45'helper_2274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'halted'45'helper_2274 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-left-setup-input-helper
d_prod'45'left'45'setup'45'input'45'helper_2276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'input'45'helper_2276 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-left-setup-mem-helper
d_prod'45'left'45'setup'45'mem'45'helper_2278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'mem'45'helper_2278 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-left-setup-saves-input
d_prod'45'left'45'setup'45'saves'45'input_2280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'saves'45'input_2280 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-right-setup-alloc-helper
d_prod'45'right'45'setup'45'alloc'45'helper_2282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'alloc'45'helper_2282 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-right-setup-halted-helper
d_prod'45'right'45'setup'45'halted'45'helper_2284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'halted'45'helper_2284 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-right-setup-input-helper
d_prod'45'right'45'setup'45'input'45'helper_2286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'input'45'helper_2286 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-right-setup-mem-helper
d_prod'45'right'45'setup'45'mem'45'helper_2288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'mem'45'helper_2288 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-setup-trace-exec
d_prod'45'setup'45'trace'45'exec_2290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'exec_2290 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-setup-trace-preserves-alloc
d_prod'45'setup'45'trace'45'preserves'45'alloc_2292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'alloc_2292 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-setup-trace-preserves-halted
d_prod'45'setup'45'trace'45'preserves'45'halted_2294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'halted_2294 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-setup-trace-preserves-heapMem
d_prod'45'setup'45'trace'45'preserves'45'heapMem_2296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'heapMem_2296 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-setup-trace-preserves-stackMem
d_prod'45'setup'45'trace'45'preserves'45'stackMem_2298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'stackMem_2298 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.prod-setup-trace-sets-input
d_prod'45'setup'45'trace'45'sets'45'input_2300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'sets'45'input_2300 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-alloc-correct-4
d_rec'45'scheme'45'alloc'45'correct'45'4_2302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'alloc'45'correct'45'4_2302 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-output-is-input
d_rec'45'scheme'45'output'45'is'45'input_2304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'output'45'is'45'input_2304 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-output-is-slot
d_rec'45'scheme'45'output'45'is'45'slot_2306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'output'45'is'45'slot_2306 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-output-is-slot-4
d_rec'45'scheme'45'output'45'is'45'slot'45'4_2308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'output'45'is'45'slot'45'4_2308 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-preserves-ancestor-3
d_rec'45'scheme'45'preserves'45'ancestor'45'3_2310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'ancestor'45'3_2310 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-preserves-ancestor-4
d_rec'45'scheme'45'preserves'45'ancestor'45'4_2312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'ancestor'45'4_2312 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-preserves-halted
d_rec'45'scheme'45'preserves'45'halted_2314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'halted_2314 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-preserves-halted-3
d_rec'45'scheme'45'preserves'45'halted'45'3_2316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'halted'45'3_2316 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-preserves-halted-4
d_rec'45'scheme'45'preserves'45'halted'45'4_2318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'halted'45'4_2318 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-preserves-heap-3
d_rec'45'scheme'45'preserves'45'heap'45'3_2320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'heap'45'3_2320 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-preserves-heap-4
d_rec'45'scheme'45'preserves'45'heap'45'4_2322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'heap'45'4_2322 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-preserves-slot-below-3
d_rec'45'scheme'45'preserves'45'slot'45'below'45'3_2324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'slot'45'below'45'3_2324 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-preserves-slot-below-4
d_rec'45'scheme'45'preserves'45'slot'45'below'45'4_2326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'slot'45'below'45'4_2326 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-stores-input
d_rec'45'scheme'45'stores'45'input_2328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'stores'45'input_2328 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-stores-input-3
d_rec'45'scheme'45'stores'45'input'45'3_2330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'stores'45'input'45'3_2330 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.rec-scheme-trace-4
d_rec'45'scheme'45'trace'45'4_2332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_rec'45'scheme'45'trace'45'4_2332 ~v0 ~v1
  = du_rec'45'scheme'45'trace'45'4_2332
du_rec'45'scheme'45'trace'45'4_2332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_rec'45'scheme'45'trace'45'4_2332 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_rec'45'scheme'45'trace'45'4_11376
      v1
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.restore-trace-preserves-alloc
d_restore'45'trace'45'preserves'45'alloc_2334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'trace'45'preserves'45'alloc_2334 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.restore-trace-preserves-heapMem
d_restore'45'trace'45'preserves'45'heapMem_2336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'trace'45'preserves'45'heapMem_2336 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.restore-trace-preserves-stackMem
d_restore'45'trace'45'preserves'45'stackMem_2338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'trace'45'preserves'45'stackMem_2338 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.setup-trace-exec
d_setup'45'trace'45'exec_2340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'exec_2340 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.setup-trace-preserves-alloc
d_setup'45'trace'45'preserves'45'alloc_2342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'alloc_2342 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.setup-trace-preserves-halted
d_setup'45'trace'45'preserves'45'halted_2344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'halted_2344 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.setup-trace-preserves-heapMem
d_setup'45'trace'45'preserves'45'heapMem_2346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'heapMem_2346 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.setup-trace-preserves-stackMem
d_setup'45'trace'45'preserves'45'stackMem_2348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'stackMem_2348 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.RecSchemeSemantics.setup-trace-sets-input
d_setup'45'trace'45'sets'45'input_2350 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'sets'45'input_2350 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SigOpEvent.ev-arg
d_ev'45'arg_2354 ::
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124 -> AgdaAny
d_ev'45'arg_2354 v0
  = coe MAlonzo.Code.Once.Denotation.Trace.d_ev'45'arg_140 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SigOpEvent.ev-dom
d_ev'45'dom_2358 ::
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_ev'45'dom_2358 v0
  = coe MAlonzo.Code.Once.Denotation.Trace.d_ev'45'dom_136 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SigOpEvent.ev-name
d_ev'45'name_2360 ::
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_ev'45'name_2360 v0
  = coe MAlonzo.Code.Once.Denotation.Trace.d_ev'45'name_134 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SigOpInfo.baseA
d_baseA_2364 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_baseA_2364 v0
  = coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SigOpInfo.conB
d_conB_2366 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_conB_2366 v0
  = coe MAlonzo.Code.Once.SigOp.Info.d_conB_184 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SigOpInfo.name
d_name_2368 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_name_2368 v0
  = coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.SigOpInfo.sem
d_sem_2370 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142
d_sem_2370 v0 = coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.InstrPreservesHalted
d_InstrPreservesHalted_2382 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.InstrWF
d_InstrWF_2384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_InstrWF_2384 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.InstrWF-frame-eq
d_InstrWF'45'frame'45'eq_2386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_InstrWF'45'frame'45'eq_2386 ~v0 ~v1
  = du_InstrWF'45'frame'45'eq_2386
du_InstrWF'45'frame'45'eq_2386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
du_InstrWF'45'frame'45'eq_2386 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_InstrWF'45'frame'45'eq_9040
      v1 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.TracePreservesHaltedP
d_TracePreservesHaltedP_2388 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.TraceWF
d_TraceWF_2390 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.TraceWF-alloc-eq
d_TraceWF'45'alloc'45'eq_2392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_TraceWF'45'alloc'45'eq_2392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_TraceWF'45'alloc'45'eq_2392 v8
du_TraceWF'45'alloc'45'eq_2392 ::
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
du_TraceWF'45'alloc'45'eq_2392 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.TraceWF-frame-eq
d_TraceWF'45'frame'45'eq_2394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_TraceWF'45'frame'45'eq_2394 ~v0 ~v1
  = du_TraceWF'45'frame'45'eq_2394
du_TraceWF'45'frame'45'eq_2394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
du_TraceWF'45'frame'45'eq_2394 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_TraceWF'45'frame'45'eq_9720
      v1 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.case-on-tag-preserves-halted
d_case'45'on'45'tag'45'preserves'45'halted_2396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'on'45'tag'45'preserves'45'halted_2396 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-abstract-preserves-halted
d_exec'45'abstract'45'preserves'45'halted_2398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrPreservesHalted_8104 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted_2398 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-abstract-preserves-halted-WF
d_exec'45'abstract'45'preserves'45'halted'45'WF_2400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted'45'WF_2400 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-abstract-state-frame-eq
d_exec'45'abstract'45'state'45'frame'45'eq_2402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'frame'45'eq_2402 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-abstract-store-at-slot-preserves-input
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'input_2404 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'input_2404
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-abstract-store-at-slot-preserves-loc
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'loc_2406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'loc_2406
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-deterministic
d_exec'45'trace'45'deterministic_2408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'deterministic_2408 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-final-lea-mov-input
d_exec'45'trace'45'final'45'lea'45'mov'45'input_2410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'final'45'lea'45'mov'45'input_2410 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-final-lea-slot
d_exec'45'trace'45'final'45'lea'45'slot_2412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'final'45'lea'45'slot_2412 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-independent
d_exec'45'trace'45'independent_2414 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'independent_2414 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-independent-below
d_exec'45'trace'45'independent'45'below_2416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'independent'45'below_2416 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-ancestor
d_exec'45'trace'45'preserves'45'ancestor_2418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'ancestor_2418 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-ancestor-nonwrite
d_exec'45'trace'45'preserves'45'ancestor'45'nonwrite_2420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'ancestor'45'nonwrite_2420 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-halted
d_exec'45'trace'45'preserves'45'halted_2422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'halted_2422 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-halted-WF
d_exec'45'trace'45'preserves'45'halted'45'WF_2424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'halted'45'WF_2424 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-heap-loc
d_exec'45'trace'45'preserves'45'heap'45'loc_2426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heap'45'loc_2426 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-heapMem
d_exec'45'trace'45'preserves'45'heapMem_2428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heapMem_2428 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-slot-above
d_exec'45'trace'45'preserves'45'slot'45'above_2430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'above_2430 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-slot-above-nonwrite
d_exec'45'trace'45'preserves'45'slot'45'above'45'nonwrite_2432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'above'45'nonwrite_2432
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-slot-below
d_exec'45'trace'45'preserves'45'slot'45'below_2434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'below_2434 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-preserves-slot-below-nonwrite
d_exec'45'trace'45'preserves'45'slot'45'below'45'nonwrite_2436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'below'45'nonwrite_2436
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-same-frame
d_exec'45'trace'45'same'45'frame_2438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'same'45'frame_2438 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-slot-value
d_exec'45'trace'45'slot'45'value_2440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'slot'45'value_2440 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-slot-value-below
d_exec'45'trace'45'slot'45'value'45'below_2442 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'slot'45'value'45'below_2442 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-snoc
d_exec'45'trace'45'snoc_2444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'snoc_2444 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-snoc-state
d_exec'45'trace'45'snoc'45'state_2446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'snoc'45'state_2446 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.exec-trace-state-frame-eq
d_exec'45'trace'45'state'45'frame'45'eq_2448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'state'45'frame'45'eq_2448 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.lea-slot-halted
d_lea'45'slot'45'halted_2482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'halted_2482 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.lea-slot-preserves-mem
d_lea'45'slot'45'preserves'45'mem_2484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'preserves'45'mem_2484 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.lea-slot-result
d_lea'45'slot'45'result_2486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'result_2486 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.load-indirect-suc-twf
d_load'45'indirect'45'suc'45'twf_2488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'twf_2488 ~v0 ~v1
  = du_load'45'indirect'45'suc'45'twf_2488
du_load'45'indirect'45'suc'45'twf_2488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'twf_2488 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'suc'45'twf_8430
      v3 v4 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.load-indirect-twf
d_load'45'indirect'45'twf_2490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'twf_2490 ~v0 ~v1
  = du_load'45'indirect'45'twf_2490
du_load'45'indirect'45'twf_2490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'twf_2490 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'twf_8412
      v3 v4 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.loop-preserves-halted
d_loop'45'preserves'45'halted_2492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loop'45'preserves'45'halted_2492 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.prefix-store-preserve
d_prefix'45'store'45'preserve_2494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prefix'45'store'45'preserve_2494 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.sigop-preserves-halted
d_sigop'45'preserves'45'halted_2496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'preserves'45'halted_2496 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.store-at-slot-halted
d_store'45'at'45'slot'45'halted_2498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'halted_2498 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.store-at-slot-preserves-other
d_store'45'at'45'slot'45'preserves'45'other_2500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'other_2500 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.store-at-slot-regs
d_store'45'at'45'slot'45'regs_2502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'regs_2502 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.store-at-slot-result
d_store'45'at'45'slot'45'result_2504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'result_2504 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.store-then-preserve
d_store'45'then'45'preserve_2506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'then'45'preserve_2506 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.tph-++
d_tph'45''43''43'_2508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8288
d_tph'45''43''43'_2508 ~v0 ~v1 = du_tph'45''43''43'_2508
du_tph'45''43''43'_2508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8288
du_tph'45''43''43'_2508 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_tph'45''43''43'_8340
      v1 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.twf-++
d_twf'45''43''43'_2514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_twf'45''43''43'_2514 ~v0 ~v1 = du_twf'45''43''43'_2514
du_twf'45''43''43'_2514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
du_twf'45''43''43'_2514 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_twf'45''43''43'_8952
      v1 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface._.TracePrimitives.twf-++-decomp
d_twf'45''43''43''45'decomp_2516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_twf'45''43''43''45'decomp_2516 ~v0 ~v1
  = du_twf'45''43''43''45'decomp_2516
du_twf'45''43''43''45'decomp_2516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_twf'45''43''43''45'decomp_2516 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_twf'45''43''43''45'decomp_8994
      v1 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ιᶠ
d_ι'7584'_2652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_ι'7584'_2652 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.evalᴰ
d_eval'7472'_2658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_2658 ~v0 v1 v2 v3 v4 = du_eval'7472'_2658 v1 v2 v3 v4
du_eval'7472'_2658 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_2658 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166 (coe v1))
      (coe
         MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166 (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_540
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v1)))
         (coe v0))
      (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.runAt
d_runAt_2662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runAt_2662 v0 ~v1 v2 v3 = du_runAt_2662 v0 v2 v3
du_runAt_2662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runAt_2662 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_run_620
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v1))
      (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.eventsAt
d_eventsAt_2670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_eventsAt_2670 v0 ~v1 v2 v3 = du_eventsAt_2670 v0 v2 v3
du_eventsAt_2670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_eventsAt_2670 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_run_620
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v1))
         (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.resultAt
d_resultAt_2678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_resultAt_2678 v0 ~v1 v2 v3 = du_resultAt_2678 v0 v2 v3
du_resultAt_2678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Res.T_Res_6
du_resultAt_2678 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_run_620
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v1))
         (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.stopsAt
d_stopsAt_2686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> Bool
d_stopsAt_2686 v0 ~v1 v2 v3 = du_stopsAt_2686 v0 v2 v3
du_stopsAt_2686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> Bool
du_stopsAt_2686 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Res.du_is'45'stopped_16
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_run_620
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v1))
            (coe v2)))
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.runAt-≡
d_runAt'45''8801'_2702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_runAt'45''8801'_2702 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.log-pure
d_log'45'pure_2710 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'pure_2710 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.log-abstract
d_log'45'abstract_2718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'abstract_2718 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.retVal
d_retVal_2726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny -> AgdaAny
d_retVal_2726 v0 ~v1 v2 ~v3 = du_retVal_2726 v0 v2
du_retVal_2726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> AgdaAny
du_retVal_2726 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.InstrWF
d_InstrWF_2734 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_InstrWF_2734 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract-preserves-halted-WF
d_exec'45'abstract'45'preserves'45'halted'45'WF_2736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted'45'WF_2736 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.load-indirect-suc-twf
d_load'45'indirect'45'suc'45'twf_2738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'twf_2738 ~v0 ~v1 ~v2
  = du_load'45'indirect'45'suc'45'twf_2738
du_load'45'indirect'45'suc'45'twf_2738 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'twf_2738 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'suc'45'twf_8430
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.load-indirect-twf
d_load'45'indirect'45'twf_2740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'twf_2740 ~v0 ~v1 ~v2
  = du_load'45'indirect'45'twf_2740
du_load'45'indirect'45'twf_2740 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'twf_2740 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'twf_8412
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_2744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_2744 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_2746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_2746 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_2748 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_2748 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_2750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_2750 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_2752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_2752 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract-load-indirect-output
d_exec'45'abstract'45'load'45'indirect'45'output_2756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'output_2756 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract-load-indirect-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_2758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_2758
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract-load-indirect-suc-output
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_2760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_2760
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract-load-indirect-suc-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_2762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_2762
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract-preserves-heap-ref
d_exec'45'abstract'45'preserves'45'heap'45'ref_2766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heap'45'ref_2766 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.CallPost
d_CallPost_2770 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatState
d_FlatState_2772 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlinkView
d_FlinkView_2776 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ProgFree
d_ProgFree_2778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_ProgFree_2778 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.Shifted
d_Shifted_2780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Shifted_2780 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.Straight
d_Straight_2782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_Straight_2782 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.StraightStep
d_StraightStep_2784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_StraightStep_2784 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.callView
d_callView_2786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350
d_callView_2786 ~v0 ~v1 v2 = du_callView_2786 v2
du_callView_2786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350
du_callView_2786 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1368 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-branch
d_do'45'branch_2792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_2792 ~v0 ~v1 v2 = du_do'45'branch_2792 v2
du_do'45'branch_2792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch_2792 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_938 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-branch-at
d_do'45'branch'45'at_2794 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch'45'at_2794 ~v0 ~v1 ~v2 = du_do'45'branch'45'at_2794
du_do'45'branch'45'at_2794 ::
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch'45'at_2794
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'branch'45'at_930
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-call
d_do'45'call_2796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_2796 ~v0 ~v1 v2 = du_do'45'call_2796 v2
du_do'45'call_2796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call_2796 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-call-at
d_do'45'call'45'at_2798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_2798 ~v0 ~v1 v2 = du_do'45'call'45'at_2798 v2
du_do'45'call'45'at_2798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'at_2798 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1284 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-call-code
d_do'45'call'45'code_2800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'code_2800 ~v0 ~v1 v2
  = du_do'45'call'45'code_2800 v2
du_do'45'call'45'code_2800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'code_2800 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'code_1292
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-call-code-prefix
d_do'45'call'45'code'45'prefix_2802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'code'45'prefix_2802 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-call-prefix
d_do'45'call'45'prefix_2804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'prefix_2804 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-call-sv
d_do'45'call'45'sv_2806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'sv_2806 ~v0 ~v1 v2 = du_do'45'call'45'sv_2806 v2
du_do'45'call'45'sv_2806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'sv_2806 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'sv_1316 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-call-sv-prefix
d_do'45'call'45'sv'45'prefix_2808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'sv'45'prefix_2808 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-jump
d_do'45'jump_2810 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_2810 ~v0 ~v1 ~v2 = du_do'45'jump_2810
du_do'45'jump_2810 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_2810
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_922
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-ret
d_do'45'ret_2812 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_2812 ~v0 ~v1 ~v2 = du_do'45'ret_2812
du_do'45'ret_2812 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_2812
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_1140
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-ret-alloc
d_do'45'ret'45'alloc_2814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_2814 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_2816 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_2816 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_2818 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_2818 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_2820 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_2820 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_2822 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_2822 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-save-closure
d_do'45'save'45'closure_2824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'save'45'closure_2824 ~v0 ~v1 ~v2
  = du_do'45'save'45'closure_2824
du_do'45'save'45'closure_2824 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'save'45'closure_2824
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1498
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.do-thunk
d_do'45'thunk_2826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_2826 ~v0 ~v1 v2 = du_do'45'thunk_2826 v2
du_do'45'thunk_2826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_2826 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1274 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.enter-call
d_enter'45'call_2828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_enter'45'call_2828 ~v0 ~v1 v2 = du_enter'45'call_2828 v2
du_enter'45'call_2828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_enter'45'call_2828 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.enter-frame
d_enter'45'frame_2830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_enter'45'frame_2830 ~v0 ~v1 v2 = du_enter'45'frame_2830 v2
du_enter'45'frame_2830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_enter'45'frame_2830 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'frame_954 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.entry-of?
d_entry'45'of'63'_2832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
d_entry'45'of'63'_2832 ~v0 ~v1 ~v2 = du_entry'45'of'63'_2832
du_entry'45'of'63'_2832 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
du_entry'45'of'63'_2832
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63'_168
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.entry-of?-sound
d_entry'45'of'63''45'sound_2834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'of'63''45'sound_2834 ~v0 ~v1 ~v2
  = du_entry'45'of'63''45'sound_2834
du_entry'45'of'63''45'sound_2834 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'of'63''45'sound_2834 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63''45'sound_634
      v0
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.entry→thunk
d_entry'8594'thunk_2836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8594'thunk_2836 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-flat
d_exec'45'flat_2838 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_2838 ~v0 ~v1 v2 = du_exec'45'flat_2838 v2
du_exec'45'flat_2838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_exec'45'flat_2838 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3630 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-flat-halted
d_exec'45'flat'45'halted_2840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_2840 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-flat-invariant
d_exec'45'flat'45'invariant_2842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_2842 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-flat-offend
d_exec'45'flat'45'offend_2844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_2844 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-flat-reloc
d_exec'45'flat'45'reloc_2846 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'flat'45'reloc_2846 ~v0 ~v1 v2
  = du_exec'45'flat'45'reloc_2846 v2
du_exec'45'flat'45'reloc_2846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'flat'45'reloc_2846 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'flat'45'reloc_3680
      (coe v0) v1 v2 v3 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-flat-step
d_exec'45'flat'45'step_2848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_2848 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_2850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_2850 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-trace-halted
d_exec'45'trace'45'halted_2852 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_2852 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_2854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_2854 ~v0 ~v1 ~v2
  = du_exec'45'trace'45'is'45'flat_2854
du_exec'45'trace'45'is'45'flat_2854 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_2854 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'trace'45'is'45'flat_4456
      v0 v1 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.falloc
d_falloc_2856 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_2856 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fclosure
d_fclosure_2858 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_2858 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fetch
d_fetch_2860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_fetch_2860 ~v0 ~v1 ~v2 = du_fetch_2860
du_fetch_2860 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
du_fetch_2860 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fetch-++-left
d_fetch'45''43''43''45'left_2862 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'left_2862 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fetch-++-right
d_fetch'45''43''43''45'right_2864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'right_2864 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fetch-All
d_fetch'45'All_2866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_2866 ~v0 ~v1 ~v2 = du_fetch'45'All_2866
du_fetch'45'All_2866 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_fetch'45'All_2866 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_4132 v1 v2 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fetch-Straight
d_fetch'45'Straight_2868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_2868 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fetch-dispatch
d_fetch'45'dispatch_2870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fetch'45'dispatch_2870 ~v0 ~v1 v2 = du_fetch'45'dispatch_2870 v2
du_fetch'45'dispatch_2870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fetch'45'dispatch_2870 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fetch'45'dispatch_3634
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.find-entry
d_find'45'entry_2872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Maybe Integer
d_find'45'entry_2872 ~v0 ~v1 v2 = du_find'45'entry_2872 v2
du_find'45'entry_2872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Maybe Integer
du_find'45'entry_2872 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'entry_228 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.find-entry-sound
d_find'45'entry'45'sound_2874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'entry'45'sound_2874 ~v0 ~v1 v2
  = du_find'45'entry'45'sound_2874 v2
du_find'45'entry'45'sound_2874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'entry'45'sound_2874 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'entry'45'sound_882
      (coe v0) v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.find-fn
d_find'45'fn_2876 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Maybe Integer
d_find'45'fn_2876 ~v0 ~v1 v2 = du_find'45'fn_2876 v2
du_find'45'fn_2876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Maybe Integer
du_find'45'fn_2876 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.find-label
d_find'45'label_2878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_2878 ~v0 ~v1 v2 = du_find'45'label_2878 v2
du_find'45'label_2878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_2878 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.find-label-lands
d_find'45'label'45'lands_2880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_2880 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.find-label-sound
d_find'45'label'45'sound_2882 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_2882 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.find-thunk
d_find'45'thunk_2884 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_2884 ~v0 ~v1 v2 = du_find'45'thunk_2884 v2
du_find'45'thunk_2884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_2884 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.find-thunk-sound
d_find'45'thunk'45'sound_2886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_2886 ~v0 ~v1 v2
  = du_find'45'thunk'45'sound_2886 v2
du_find'45'thunk'45'sound_2886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'sound_2886 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk'45'sound_916
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fl-at
d_fl'45'at_2888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_2888 ~v0 ~v1 v2 = du_fl'45'at_2888 v2
du_fl'45'at_2888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'at_2888 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'at_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fl-at-++-miss
d_fl'45'at'45''43''43''45'miss_2890 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'at'45''43''43''45'miss_2890 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fl-go
d_fl'45'go_2892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_2892 ~v0 ~v1 v2 = du_fl'45'go_2892 v2
du_fl'45'go_2892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'go_2892 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fl-go-++-miss
d_fl'45'go'45''43''43''45'miss_2894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45''43''43''45'miss_2894 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fl-go-lands
d_fl'45'go'45'lands_2896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_2896 ~v0 ~v1 v2 = du_fl'45'go'45'lands_2896 v2
du_fl'45'go'45'lands_2896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_2896 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'lands_3916
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fl-go-sound
d_fl'45'go'45'sound_2898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_2898 ~v0 ~v1 v2 = du_fl'45'go'45'sound_2898 v2
du_fl'45'go'45'sound_2898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_2898 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'sound_762
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fl-label-match
d_fl'45'label'45'match_2900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_2900 ~v0 ~v1 v2
  = du_fl'45'label'45'match_2900 v2
du_fl'45'label'45'match_2900 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'label'45'match_2900 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fl-match-++-miss
d_fl'45'match'45''43''43''45'miss_2902 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'match'45''43''43''45'miss_2902 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-exec-instr
d_flat'45'exec'45'instr_2904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_2904 ~v0 ~v1 v2
  = du_flat'45'exec'45'instr_2904 v2
du_flat'45'exec'45'instr_2904 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_2904 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-exec-instr-prefix
d_flat'45'exec'45'instr'45'prefix_2906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prefix_2906 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-exec-instr-prog-irrelevant
d_flat'45'exec'45'instr'45'prog'45'irrelevant_2908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prog'45'irrelevant_2908 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-halt
d_flat'45'halt_2910 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'halt_2910 ~v0 ~v1 ~v2 = du_flat'45'halt_2910
du_flat'45'halt_2910 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'halt_2910
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'halt_1280
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-read-at
d_flat'45'read'45'at_2912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'at_2912 ~v0 ~v1 ~v2 = du_flat'45'read'45'at_2912
du_flat'45'read'45'at_2912 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'at_2912
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'at_110
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-read-tag
d_flat'45'read'45'tag_2914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_2914 ~v0 ~v1 ~v2
  = du_flat'45'read'45'tag_2914
du_flat'45'read'45'tag_2914 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_2914
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-step-frame
d_flat'45'step'45'frame_2916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'frame_2916 ~v0 ~v1 v2
  = du_flat'45'step'45'frame_2916 v2
du_flat'45'step'45'frame_2916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'frame_2916 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'frame_1132
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-step-straight
d_flat'45'step'45'straight_2918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'straight_2918 ~v0 ~v1 v2
  = du_flat'45'step'45'straight_2918 v2
du_flat'45'step'45'straight_2918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'straight_2918 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flink
d_flink_2920 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_2920 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flink-do-branch
d_flink'45'do'45'branch_2922 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch_2922 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flink-do-jump
d_flink'45'do'45'jump_2924 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'jump_2924 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flink-do-ret
d_flink'45'do'45'ret_2926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'ret_2926 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flinkView
d_flinkView_2928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3448
d_flinkView_2928 ~v0 ~v1 ~v2 = du_flinkView_2928
du_flinkView_2928 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3448
du_flinkView_2928
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flinkView_3476
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.floc
d_floc_2930 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_2930 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.forced
d_forced_2932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_forced_2932 ~v0 ~v1 ~v2 = du_forced_2932
du_forced_2932 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_forced_2932
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_4446
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fpc
d_fpc_2934 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_2934 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.fret
d_fret_2936 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_2936 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-at
d_ft'45'at_2938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'at_2938 ~v0 ~v1 v2 = du_ft'45'at_2938 v2
du_ft'45'at_2938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'at_2938 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'at_194 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-at-++-miss
d_ft'45'at'45''43''43''45'miss_2940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45''43''43''45'miss_2940 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-at-prefix
d_ft'45'at'45'prefix_2942 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45'prefix_2942 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-go
d_ft'45'go_2944 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'go_2944 ~v0 ~v1 v2 = du_ft'45'go_2944 v2
du_ft'45'go_2944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'go_2944 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_192 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-go-++-miss
d_ft'45'go'45''43''43''45'miss_2946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45''43''43''45'miss_2946 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-go-prefix
d_ft'45'go'45'prefix_2948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45'prefix_2948 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-go-sound
d_ft'45'go'45'sound_2950 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_2950 ~v0 ~v1 v2 = du_ft'45'go'45'sound_2950 v2
du_ft'45'go'45'sound_2950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_2950 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_ft'45'go'45'sound_654
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-match
d_ft'45'match_2952 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'match_2952 ~v0 ~v1 v2 = du_ft'45'match_2952 v2
du_ft'45'match_2952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'match_2952 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_196 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-match-++-miss
d_ft'45'match'45''43''43''45'miss_2954 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45''43''43''45'miss_2954 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ft-match-prefix
d_ft'45'match'45'prefix_2956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45'prefix_2956 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.grow-frame
d_grow'45'frame_2968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_grow'45'frame_2968 ~v0 ~v1 v2 = du_grow'45'frame_2968 v2
du_grow'45'frame_2968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_grow'45'frame_2968 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_grow'45'frame_1268 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.just-injℕ
d_just'45'injℕ_2970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_2970 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.lab-eq
d_lab'45'eq_2972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_2972 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.label-of?
d_label'45'of'63'_2974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_2974 ~v0 ~v1 ~v2 = du_label'45'of'63'_2974
du_label'45'of'63'_2974 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_2974
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_122
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.label-of?-sound
d_label'45'of'63''45'sound_2976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_2976 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.leave-frame
d_leave'45'frame_2978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_leave'45'frame_2978 ~v0 ~v1 ~v2 = du_leave'45'frame_2978
du_leave'45'frame_2978 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_leave'45'frame_2978
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_976
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.leave-frame-aux
d_leave'45'frame'45'aux_2980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_leave'45'frame'45'aux_2980 ~v0 ~v1 ~v2
  = du_leave'45'frame'45'aux_2980
du_leave'45'frame'45'aux_2980 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_leave'45'frame'45'aux_2980
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_964
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.leave-frame-block-size
d_leave'45'frame'45'block'45'size_2982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_2982 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_2984 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_2984 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_2986 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_2986 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_2988 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_2988 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_2990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_2990 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_2992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_2992 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_2994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_2994 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.mkFlat
d_mkFlat_2996 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_mkFlat_2996 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v0)
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.reloc-fetch
d_reloc'45'fetch_3000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'fetch_3000 ~v0 ~v1 v2 = du_reloc'45'fetch_3000 v2
du_reloc'45'fetch_3000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'fetch_3000 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'fetch_3724 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.reloc-step
d_reloc'45'step_3002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'step_3002 ~v0 ~v1 v2 = du_reloc'45'step_3002 v2
du_reloc'45'step_3002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'step_3002 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'step_3702 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shift
d_shift_3004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_shift_3004 ~v0 ~v1 ~v2 = du_shift_3004
du_shift_3004 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_shift_3004
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shift_3374
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shift-loc
d_shift'45'loc_3006 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_3006 ~v0 ~v1 v2 = du_shift'45'loc_3006 v2
du_shift'45'loc_3006 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_3006 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shift'45'loc_4298 (coe v0) v1
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-branch
d_shifted'45'branch_3008 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'branch_3008 ~v0 ~v1 ~v2 = du_shifted'45'branch_3008
du_shifted'45'branch_3008 ::
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
du_shifted'45'branch_3008 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'branch_1824 v1 v4
      v7
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-call-at
d_shifted'45'call'45'at_3010 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'call'45'at_3010 ~v0 ~v1 ~v2
  = du_shifted'45'call'45'at_3010
du_shifted'45'call'45'at_3010 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'at_3010 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'at_1962 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-call-closure
d_shifted'45'call'45'closure_3012 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'closure_3012 ~v0 ~v1 v2
  = du_shifted'45'call'45'closure_3012 v2
du_shifted'45'call'45'closure_3012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'closure_3012 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'closure_2178
      (coe v0) v3 v4 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-call-code
d_shifted'45'call'45'code_3014 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'code_3014 ~v0 ~v1 v2
  = du_shifted'45'call'45'code_3014 v2
du_shifted'45'call'45'code_3014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'code_3014 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'code_2010
      (coe v0) v2 v4 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-call-sv
d_shifted'45'call'45'sv_3016 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'sv_3016 ~v0 ~v1 v2
  = du_shifted'45'call'45'sv_3016 v2
du_shifted'45'call'45'sv_3016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'sv_3016 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'sv_2092
      (coe v0) v2 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-eq
d_shifted'45'eq_3018 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shifted'45'eq_3018 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-frame
d_shifted'45'frame_3020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'frame_3020 ~v0 ~v1 ~v2 = du_shifted'45'frame_3020
du_shifted'45'frame_3020 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'frame_3020 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'frame_1862 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-halt
d_shifted'45'halt_3022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'halt_3022 ~v0 ~v1 ~v2 = du_shifted'45'halt_3022
du_shifted'45'halt_3022 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'halt_3022 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'halt_1928 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-instr
d_shifted'45'instr_3024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'instr_3024 ~v0 ~v1 v2 = du_shifted'45'instr_3024 v2
du_shifted'45'instr_3024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'instr_3024 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'instr_2218
      (coe v0) v2 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-jump
d_shifted'45'jump_3026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'jump_3026 ~v0 ~v1 ~v2 = du_shifted'45'jump_3026
du_shifted'45'jump_3026 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'jump_3026 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'jump_1766 v2 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-label
d_shifted'45'label_3028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'label_3028 ~v0 ~v1 ~v2 = du_shifted'45'label_3028
du_shifted'45'label_3028 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'label_3028 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'label_1624 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-ret
d_shifted'45'ret_3030 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret_3030 ~v0 ~v1 ~v2 = du_shifted'45'ret_3030
du_shifted'45'ret_3030 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret_3030 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret_1742 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-ret-aux
d_shifted'45'ret'45'aux_3032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'ret'45'aux_3032 ~v0 ~v1 ~v2
  = du_shifted'45'ret'45'aux_3032
du_shifted'45'ret'45'aux_3032 ::
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret'45'aux_3032 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret'45'aux_1690 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-save-closure
d_shifted'45'save'45'closure_3034 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'save'45'closure_3034 ~v0 ~v1 ~v2
  = du_shifted'45'save'45'closure_3034
du_shifted'45'save'45'closure_3034 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'save'45'closure_3034 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'save'45'closure_1900
      v3
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-shift
d_shifted'45'shift_3036 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'shift_3036 ~v0 ~v1 ~v2 = du_shifted'45'shift_3036
du_shifted'45'shift_3036 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'shift_3036 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'shift_3388
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-straight
d_shifted'45'straight_3038 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'straight_3038 ~v0 ~v1 ~v2
  = du_shifted'45'straight_3038
du_shifted'45'straight_3038 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'straight_3038 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'straight_1588 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.shifted-thunk
d_shifted'45'thunk_3040 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'thunk_3040 ~v0 ~v1 ~v2 = du_shifted'45'thunk_3040
du_shifted'45'thunk_3040 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'thunk_3040 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'thunk_1652 v4
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.step-dispatch
d_step'45'dispatch_3042 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_step'45'dispatch_3042 ~v0 ~v1 v2 = du_step'45'dispatch_3042 v2
du_step'45'dispatch_3042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_step'45'dispatch_3042 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_step'45'dispatch_3632 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.sv-is-zero
d_sv'45'is'45'zero_3044 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_3044 ~v0 ~v1 ~v2 = du_sv'45'is'45'zero_3044
du_sv'45'is'45'zero_3044 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_3044
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.tag-zf
d_tag'45'zf_3046 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_3046 ~v0 ~v1 ~v2 = du_tag'45'zf_3046
du_tag'45'zf_3046 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_3046
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.thunk-of?
d_thunk'45'of'63'_3048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_3048 ~v0 ~v1 ~v2 = du_thunk'45'of'63'_3048
du_thunk'45'of'63'_3048 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_3048
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63'_176
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.thunk-of?-sound
d_thunk'45'of'63''45'sound_3050 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_3050 ~v0 ~v1 ~v2
  = du_thunk'45'of'63''45'sound_3050
du_thunk'45'of'63''45'sound_3050 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_3050 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63''45'sound_620
      v0
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.thunk-part
d_thunk'45'part_3052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'part_3052 ~v0 ~v1 ~v2 = du_thunk'45'part_3052
du_thunk'45'part_3052 ::
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'part_3052
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'part_172
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.≡ᵇ-true
d_'8801''7495''45'true_3054 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_3054 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatState.falloc
d_falloc_3064 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_3064 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatState.fclosure
d_fclosure_3066 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_3066 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatState.flink
d_flink_3068 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_3068 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatState.floc
d_floc_3070 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_3070 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatState.fpc
d_fpc_3072 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_3072 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatState.fret
d_fret_3074 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_3074 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.log-step
d_log'45'step_3094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'step_3094 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatSteps
d_FlatSteps_3108 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatSteps-++
d_FlatSteps'45''43''43'_3110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_FlatSteps'45''43''43'_3110 ~v0 ~v1 ~v2
  = du_FlatSteps'45''43''43'_3110
du_FlatSteps'45''43''43'_3110 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_FlatSteps'45''43''43'_3110 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1192
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatSteps-prefix
d_FlatSteps'45'prefix_3112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_FlatSteps'45'prefix_3112 ~v0 ~v1 ~v2
  = du_FlatSteps'45'prefix_3112
du_FlatSteps'45'prefix_3112 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_FlatSteps'45'prefix_3112 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'prefix_1020
      v6
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.FlatSteps-reloc
d_FlatSteps'45'reloc_3114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_FlatSteps'45'reloc_3114 ~v0 ~v1 ~v2 = du_FlatSteps'45'reloc_3114
du_FlatSteps'45'reloc_3114 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_FlatSteps'45'reloc_3114 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'reloc_1062
      v6
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-flat-steps
d_exec'45'flat'45'steps_3118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_3118 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.step-at
d_step'45'at_3120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_step'45'at_3120 ~v0 ~v1 ~v2 = du_step'45'at_3120
du_step'45'at_3120 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_step'45'at_3120 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_388 v4
      v6 v8
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-abstract
d_exec'45'abstract_3130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_3130 ~v0 ~v1 v2 = du_exec'45'abstract_3130 v2
du_exec'45'abstract_3130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_3130 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-sigop-halts
d_exec'45'sigop'45'halts_3132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_3132 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts_3132
du_exec'45'sigop'45'halts_3132 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts_3132 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_3126
      v2
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_3134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_3134 ~v0 ~v1 ~v2
  = du_exec'45'sigop'45'halts'45'of_3134
du_exec'45'sigop'45'halts'45'of_3134 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts'45'of_3134 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_3120
      v2
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_3136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_3136 ~v0 ~v1 v2
  = du_exec'45'sigop'45'output'45'of_3136 v2
du_exec'45'sigop'45'output'45'of_3136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_3136 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_3068
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_3138 ::
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
d_pure'45'sigop'45'out'45'aux_3138 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'aux_3138 v2
du_pure'45'sigop'45'out'45'aux_3138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'aux_3138 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_3032
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_3140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_3140 ~v0 ~v1 v2
  = du_pure'45'sigop'45'out'45'val_3140 v2
du_pure'45'sigop'45'out'45'val_3140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_3140 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'val_3008
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.pure-sigop-output
d_pure'45'sigop'45'output_3142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_3142 ~v0 ~v1 v2
  = du_pure'45'sigop'45'output_3142 v2
du_pure'45'sigop'45'output_3142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'output_3142 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_3002
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.readReg-typed
d_readReg'45'typed_3144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_3144 ~v0 ~v1 ~v2 = du_readReg'45'typed_3144
du_readReg'45'typed_3144 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_3144
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2762
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.readTyped
d_readTyped_3146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_readTyped_3146 ~v0 ~v1 ~v2 = du_readTyped_3146
du_readTyped_3146 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_readTyped_3146
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2818
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.BeforeFrontier
d_BeforeFrontier_3150 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.frontier-monotone
d_frontier'45'monotone_3152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_frontier'45'monotone_3152 ~v0 ~v1 ~v2
  = du_frontier'45'monotone_3152
du_frontier'45'monotone_3152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_frontier'45'monotone_3152 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.CellAt
d_CellAt_3164 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.EnvAt
d_EnvAt_3166 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.InlineRep
d_InlineRep_3168 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ResultPlace
d_ResultPlace_3170 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ValidAtWF
d_ValidAtWF_3172 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.decomposeClosureWF
d_decomposeClosureWF_3182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682
d_decomposeClosureWF_3182 ~v0 ~v1 ~v2 = du_decomposeClosureWF_3182
du_decomposeClosureWF_3182 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682
du_decomposeClosureWF_3182 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1752
      v7
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.decomposePairWF
d_decomposePairWF_3184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906
d_decomposePairWF_3184 ~v0 ~v1 ~v2 = du_decomposePairWF_3184
du_decomposePairWF_3184 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906
du_decomposePairWF_3184 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1948
      v7
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.inline-sv
d_inline'45'sv_3190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_590 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_3190 ~v0 ~v1 ~v2 = du_inline'45'sv_3190
du_inline'45'sv_3190 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_590 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_3190 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_600
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.prim-sv
d_prim'45'sv_3192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_3192 ~v0 ~v1 ~v2 = du_prim'45'sv_3192
du_prim'45'sv_3192 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_3192 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_582
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.valid-primitive-wf
d_valid'45'primitive'45'wf_3214 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_valid'45'primitive'45'wf_3214 ~v0 ~v1 ~v2
  = du_valid'45'primitive'45'wf_3214
du_valid'45'primitive'45'wf_3214 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_valid'45'primitive'45'wf_3214 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'primitive'45'wf_632
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_3220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'frontier'45'advance_3220 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4440
      (coe v0) (coe v1) (coe v2) v4 v5 v6 v7 v8 v9 v11 v12 v13
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_3222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'mem'45'preserved_3222 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                      v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
      (coe v0) (coe v1) (coe v2) v4 v5 v6 v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_3224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'with'45'bf'45'transfer_3224 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'with'45'bf'45'transfer_4856
      (coe v0) (coe v1) (coe v2) v4 v5 v6 v7 v8 v9 v10 v11
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ClosureValidWF.EnvType
d_EnvType_3234 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_3234 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_EnvType_1716
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ClosureValidWF.body
d_body_3236 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_body_3236 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body_1718
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ClosureValidWF.body-label
d_body'45'label_3238 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_3238 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'label_1722
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ClosureValidWF.code-ptr
d_code'45'ptr_3240 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_3240 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ClosureValidWF.env
d_env_3242 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  AgdaAny
d_env_3242 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env_1720 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ClosureValidWF.env-at
d_env'45'at_3244 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1648
d_env'45'at_3244 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'at_1726
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_3246 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_3246 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ClosureValidWF.loc-mode
d_loc'45'mode_3248 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  AgdaAny
d_loc'45'mode_3248 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_loc'45'mode_1724
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_3250 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_3250 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1730
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.PairValidWF.fst-cell
d_fst'45'cell_3266 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612
d_fst'45'cell_3266 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.PairValidWF.snd-cell
d_snd'45'cell_3268 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612
d_snd'45'cell_3268 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1930
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.PairValidWF.sucLoc-before
d_sucLoc'45'before_3270 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_3270 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1926
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.readLoc
d_readLoc_3308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_3308 ~v0 ~v1 ~v2 = du_readLoc_3308
du_readLoc_3308 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_3308
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_3312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_3312 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.chain-events
d_chain'45'events_3316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_chain'45'events_3316 ~v0 ~v1 v2 = du_chain'45'events_3316 v2
du_chain'45'events_3316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_chain'45'events_3316 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_604
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.chain-events-++
d_chain'45'events'45''43''43'_3318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_3318 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.chain-events-nil
d_chain'45'events'45'nil_3320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_3320 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.chain-events-subst-start
d_chain'45'events'45'subst'45'start_3322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_3322 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.event-of
d_event'45'of_3324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_event'45'of_3324 ~v0 ~v1 ~v2 = du_event'45'of_3324
du_event'45'of_3324 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_event'45'of_3324
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_458
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-events
d_flat'45'events_3326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'events_3326 ~v0 ~v1 v2 = du_flat'45'events_3326 v2
du_flat'45'events_3326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'events_3326 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_464 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.flat-events-[]
d_flat'45'events'45''91''93'_3328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_3328 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ChainNotNested
d_ChainNotNested_3332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 -> ()
d_ChainNotNested_3332 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.chain-log
d_chain'45'log_3334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'log_3334 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.log-of
d_log'45'of_3348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'of_3348 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.log-silent
d_log'45'silent_3370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'45'silent_3370 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.Readable
d_Readable_3382 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.readTyped-adequate
d_readTyped'45'adequate_3398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'adequate_3398 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.readable-base
d_readable'45'base_3400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890
d_readable'45'base_3400 ~v0 ~v1 ~v2 = du_readable'45'base_3400
du_readable'45'base_3400 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890
du_readable'45'base_3400
  = coe
      MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'45'base_920
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.readable?
d_readable'63'_3402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890
d_readable'63'_3402 ~v0 ~v1 ~v2 = du_readable'63'_3402
du_readable'63'_3402 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_890
du_readable'63'_3402
  = coe
      MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'63'_932
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.AllSlotStable
d_AllSlotStable_3422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_AllSlotStable_3422 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.exec-flat-keeps-next-slot
d_exec'45'flat'45'keeps'45'next'45'slot_3424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'keeps'45'next'45'slot_3424 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ir-stable
d_ir'45'stable_3428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_3428 v0 ~v1 v2 = du_ir'45'stable_3428 v0 v2
du_ir'45'stable_3428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'stable_3428 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'stable_524
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core._.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_3430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_3430 v0 ~v1 v2
  = du_ir'45'to'45'trace'45'slot'45'stable_3430 v0 v2
du_ir'45'to'45'trace'45'slot'45'stable_3430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'slot'45'stable_3430 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_856
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.μ-layer-iso
d_μ'45'layer'45'iso_3446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_μ'45'layer'45'iso_3446 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         v10
  = du_μ'45'layer'45'iso_3446 v10
du_μ'45'layer'45'iso_3446 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_μ'45'layer'45'iso_3446 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_1018 v6 v8
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.emitted
d_emitted_3464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_emitted_3464 v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_emitted_3464 v0 v3 v4 v5 v6 v7
du_emitted_3464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_emitted_3464 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))))
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.blocks
d_blocks_3476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_3476 v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_blocks_3476 v0 v3 v4 v5 v6 v7
du_blocks_3476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_blocks_3476 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))))
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.entry-flat
d_entry'45'flat_3484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_entry'45'flat_3484 ~v0 v1 v2 v3 v4
  = du_entry'45'flat_3484 v1 v2 v3 v4
du_entry'45'flat_3484 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_entry'45'flat_3484 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v1)
      (coe v2) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.SpanAt
d_SpanAt_3494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_SpanAt_3494 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.LabelsAt
d_LabelsAt_3506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_LabelsAt_3506 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.BlockAt
d_BlockAt_3518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockAt_3518 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.BlocksAt
d_BlocksAt_3528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_BlocksAt_3528 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.flat-run
d_flat'45'run_3534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'run_3534 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3630 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v4)
         (coe v5) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.flat-run-keeps-next-slot
d_flat'45'run'45'keeps'45'next'45'slot_3560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'run'45'keeps'45'next'45'slot_3560 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized
d_ValueRealized_3600 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14
  = ()
data T_ValueRealized_3600
  = C_realized_3714 Integer
                    MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
                    MAlonzo.Code.Once.IR.T_AllocMode_4
                    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
                    MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
                    (AgdaAny ->
                     MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                     MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646)
                    (Integer ->
                     MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.steps
d_steps_3670 :: T_ValueRealized_3600 -> Integer
d_steps_3670 v0
  = case coe v0 of
      C_realized_3714 v1 v2 v3 v4 v5 v12 v16 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.settle
d_settle_3672 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_3672 v0
  = case coe v0 of
      C_realized_3714 v1 v2 v3 v4 v5 v12 v16 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.out-mode
d_out'45'mode_3674 ::
  T_ValueRealized_3600 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_3674 v0
  = case coe v0 of
      C_realized_3714 v1 v2 v3 v4 v5 v12 v16 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.cont-alloc
d_cont'45'alloc_3676 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_3676 v0
  = case coe v0 of
      C_realized_3714 v1 v2 v3 v4 v5 v12 v16 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.run
d_run_3678 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_3678 v0
  = case coe v0 of
      C_realized_3714 v1 v2 v3 v4 v5 v12 v16 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.live
d_live_3680 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_3680 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.at-end
d_at'45'end_3682 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_3682 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.stops
d_stops_3684 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_3684 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.no-ret
d_no'45'ret_3686 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_3686 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.no-link
d_no'45'link_3688 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_3688 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.log
d_log_3690 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_3690 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.place
d_place_3694 ::
  T_ValueRealized_3600 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_3694 v0
  = case coe v0 of
      C_realized_3714 v1 v2 v3 v4 v5 v12 v16 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.stack-pres
d_stack'45'pres_3700 ::
  T_ValueRealized_3600 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_3700 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.heap-pres
d_heap'45'pres_3704 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_3704 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.frame-pres
d_frame'45'pres_3706 ::
  T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_3706 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.ValueRealized.bf-mono
d_bf'45'mono_3712 ::
  T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_3712 v0
  = case coe v0 of
      C_realized_3714 v1 v2 v3 v4 v5 v12 v16 -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.vr-mem-pres
d_vr'45'mem'45'pres_3744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vr'45'mem'45'pres_3744 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.MachineRefinesObsF
d_MachineRefinesObsF_3784 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14
  = ()
newtype T_MachineRefinesObsF_3784
  = C_constructor_3818 T_ValueRealized_3600
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.MachineRefinesObsF.value-realized
d_value'45'realized_3814 ::
  T_MachineRefinesObsF_3784 -> T_ValueRealized_3600
d_value'45'realized_3814 v0
  = case coe v0 of
      C_constructor_3818 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.MachineRefinesObsF.traces-agree
d_traces'45'agree_3816 ::
  T_MachineRefinesObsF_3784 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_3816 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.InputAt
d_InputAt_3830 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InputAt_3830
  = C_in'45'loc_3844 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                     MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 |
    C_in'45'reg_3848 MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 |
    C_in'45'unit_3850
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun
d_CalleeRun_3864 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_CalleeRun_3864
  = C_callee'45'run_3974 Integer
                         MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
                         MAlonzo.Code.Once.IR.T_AllocMode_4
                         MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
                         MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
                         (AgdaAny ->
                          MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646)
                         (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
                          Integer ->
                          MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                          MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                          MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
                          MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.steps
d_steps_3926 :: T_CalleeRun_3864 -> Integer
d_steps_3926 v0
  = case coe v0 of
      C_callee'45'run_3974 v1 v2 v3 v4 v5 v11 v16 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.settle
d_settle_3928 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_3928 v0
  = case coe v0 of
      C_callee'45'run_3974 v1 v2 v3 v4 v5 v11 v16 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.out-mode
d_out'45'mode_3930 ::
  T_CalleeRun_3864 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_3930 v0
  = case coe v0 of
      C_callee'45'run_3974 v1 v2 v3 v4 v5 v11 v16 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.cont-alloc
d_cont'45'alloc_3932 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_3932 v0
  = case coe v0 of
      C_callee'45'run_3974 v1 v2 v3 v4 v5 v11 v16 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.run
d_run_3934 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_3934 v0
  = case coe v0 of
      C_callee'45'run_3974 v1 v2 v3 v4 v5 v11 v16 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.live
d_live_3936 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_3936 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.returned
d_returned_3938 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_3938 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.stops
d_stops_3940 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_3940 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.no-ret
d_no'45'ret_3942 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_3942 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.no-link
d_no'45'link_3944 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_3944 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.place
d_place_3948 ::
  T_CalleeRun_3864 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_3948 v0
  = case coe v0 of
      C_callee'45'run_3974 v1 v2 v3 v4 v5 v11 v16 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.events
d_events_3950 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_3950 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.log
d_log_3952 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_3952 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.mem-pres
d_mem'45'pres_3960 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_3960 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.frame-pres
d_frame'45'pres_3964 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_3964 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRun.bf-mono
d_bf'45'mono_3972 ::
  T_CalleeRun_3864 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_3972 v0
  = case coe v0 of
      C_callee'45'run_3974 v1 v2 v3 v4 v5 v11 v16 -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CalleeRuns
d_CalleeRuns_3976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_CalleeRuns_3976 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.CoalgRuns
d_CoalgRuns_4016 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_CoalgRuns_4016 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.FnRuns
d_FnRuns_4052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_FnRuns_4052 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.BlockRuns
d_BlockRuns_4078 a0 a1 a2 a3 = ()
data T_BlockRuns_4078
  = C_constructor_4094 (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                        MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                        MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                        MAlonzo.Code.Once.IR.T_IR_16 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
                        MAlonzo.Code.Once.IR.T_AllocMode_4 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
                        MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                       (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                        MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
                        MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
                        MAlonzo.Code.Once.IR.T_IR_16 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
                        MAlonzo.Code.Once.IR.T_AllocMode_4 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
                        MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                       (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
                        MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                        MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                        AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.BlockRuns.closures
d_closures_4088 ::
  T_BlockRuns_4078 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closures_4088 v0
  = case coe v0 of
      C_constructor_4094 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.BlockRuns.coalgs
d_coalgs_4090 ::
  T_BlockRuns_4078 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coalgs_4090 v0
  = case coe v0 of
      C_constructor_4094 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.BlockRuns.functions
d_functions_4092 ::
  T_BlockRuns_4078 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_functions_4092 v0
  = case coe v0 of
      C_constructor_4094 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.IRObsCorrectF
d_IRObsCorrectF_4100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_4100 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.cata-correct
d_cata'45'correct_4138
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Interface.Core.cata-correct"
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.exec-flat-stop
d_exec'45'flat'45'stop_4146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'stop_4146 = erased
-- Once.CCC.Codegen.IRObsCorrect.Interface.Core.reg-write-readLoc
d_reg'45'write'45'readLoc_4174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'write'45'readLoc_4174 = erased
