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
import qualified MAlonzo.Code.Agda.Builtin.String
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
import qualified MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Prelude
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotBudget
import qualified MAlonzo.Code.Once.CCC.Eval
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
import qualified MAlonzo.Code.Once.CCC.Machine.Validity
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
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
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Codegen.IRObsCorrect.Machine._.Σ
d_Σ_1 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractReg
d_AbstractReg_3 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InitLast
d_InitLast_5 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Bool
d_Bool_7 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⊤
d_'8868'_9 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.budget-of
d_budget'45'of_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_14 ~v0 = du_budget'45'of_14
du_budget'45'of_14 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_budget'45'of_14
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_budget'45'of_74
-- Once.CCC.Codegen.IRObsCorrect.Machine._.fits-erase
d_fits'45'erase_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526
d_fits'45'erase_16 ~v0 = du_fits'45'erase_16
du_fits'45'erase_16 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526
du_fits'45'erase_16 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Prelude.du_fits'45'erase_14
      v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.frontier-mono
d_frontier'45'mono_18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_18 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotBudget.d_frontier'45'mono_870
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ir-to-trace
d_ir'45'to'45'trace_20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_ir'45'to'45'trace_20 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_812
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ir-to-trace'
d_ir'45'to'45'trace''_22 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_22 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_488
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.validAtWF-set-halted
d_validAtWF'45'set'45'halted_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validAtWF'45'set'45'halted_24 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ValidAtWFHalted.du_validAtWF'45'set'45'halted_1330
      (coe v0) v1 v3 v4 v5 v7 v8 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.AllI→All
d_AllI'8594'All_28 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_AllI'8594'All_28 ~v0 = du_AllI'8594'All_28
du_AllI'8594'All_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_AllI'8594'All_28 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_AllI'8594'All_156
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.All→AllI
d_All'8594'AllI_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_All'8594'AllI_30 ~v0 = du_All'8594'AllI_30
du_All'8594'AllI_30 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_All'8594'AllI_30 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_All'8594'AllI_102
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.BlockStable
d_BlockStable_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockStable_32 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.all-stable?
d_all'45'stable'63'_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> Bool
d_all'45'stable'63'_34 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_all'45'stable'63'_110
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.all-stable?-++
d_all'45'stable'63''45''43''43'_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45''43''43'_36 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.all-stable?-complete
d_all'45'stable'63''45'complete_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45'complete_38 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.all-stable?-sound
d_all'45'stable'63''45'sound_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'stable'63''45'sound_40 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_all'45'stable'63''45'sound_132
      (coe v0) v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.bds
d_bds_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bds_42 ~v0 = du_bds_42
du_bds_42 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_bds_42 v0 v1
  = coe MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_bds_642 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.blocks-stable
d_blocks'45'stable_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'stable_44 ~v0 = du_blocks'45'stable_44
du_blocks'45'stable_44 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'stable_44 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_blocks'45'stable_652
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-body-stable
d_cata'45'body'45'stable_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'body'45'stable_46 ~v0 = du_cata'45'body'45'stable_46
du_cata'45'body'45'stable_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'body'45'stable_46 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'body'45'stable_350
      v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-dispatch-slot-stable
d_cata'45'dispatch'45'slot'45'stable_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'dispatch'45'slot'45'stable_48 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'dispatch'45'slot'45'stable_466
      (coe v0) v1 v2 v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-trace-branching-stable
d_cata'45'trace'45'branching'45'stable_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'branching'45'stable_50 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'branching'45'stable_432
      (coe v0) v1 v2 v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-trace-const-stable
d_cata'45'trace'45'const'45'stable_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'const'45'stable_52 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'const'45'stable_370
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-trace-linear-stable
d_cata'45'trace'45'linear'45'stable_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'linear'45'stable_54 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'linear'45'stable_410
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.cata-trace-nat-stable
d_cata'45'trace'45'nat'45'stable_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'nat'45'stable_56 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'nat'45'stable_390
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.ir-blocks-stable
d_ir'45'blocks'45'stable_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'blocks'45'stable_58 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'blocks'45'stable_746
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.ir-stable
d_ir'45'stable_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_60 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'stable_520
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_62 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_876
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.rebuild-walk-stable
d_rebuild'45'walk'45'stable_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'walk'45'stable_64 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_rebuild'45'walk'45'stable_292
      (coe v0) v1 v2 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.resuspend-stable
d_resuspend'45'stable_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_resuspend'45'stable_66 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_resuspend'45'stable_676
      (coe v0) v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.stable?
d_stable'63'_68 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> Bool
d_stable'63'_68 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_stable'63'_108
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.stable?-complete
d_stable'63''45'complete_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable'63''45'complete_70 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.stable?-sound
d_stable'63''45'sound_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_stable'63''45'sound_72 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_stable'63''45'sound_128
      (coe v0) v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.trc
d_trc_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_trc_74 ~v0 = du_trc_74
du_trc_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_trc_74 v0 v1
  = coe MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_trc_96 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.visit-walk-stable
d_visit'45'walk'45'stable_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_visit'45'walk'45'stable_76 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_visit'45'walk'45'stable_230
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.∧-intro
d_'8743''45'intro_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'intro_78 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataIRSlotStable.∧-split
d_'8743''45'split_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_80 ~v0 = du_'8743''45'split_80
du_'8743''45'split_80 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_80 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_'8743''45'split_124
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.BodyCorrect
d_BodyCorrect_86 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.CellAt
d_CellAt_90 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.CellLocsInRegions
d_CellLocsInRegions_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584 -> ()
d_CellLocsInRegions_92 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF
d_ClosureValidWF_94 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed
d_ClosureWellFormed_98 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                       a13
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.EnvAt
d_EnvAt_102 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget
d_IRHeapBudget_104 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF
d_IRResultAWF_108 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase
d_IRResultBase_112 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget
d_IRStackBudget_116 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF
d_InlValidWF_122 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlineRep
d_InlineRep_126 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InputPlace
d_InputPlace_128 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF
d_InrValidWF_130 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.LocInRegions
d_LocInRegions_134 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.LocsInRegions
d_LocsInRegions_136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  ()
d_LocsInRegions_136 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PairValidWF
d_PairValidWF_138 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PayloadAt
d_PayloadAt_142 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.Place
d_Place_144 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.RecDispatcherWF
d_RecDispatcherWF_146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> ()
d_RecDispatcherWF_146 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ResultPlace
d_ResultPlace_148 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.SumTag
d_SumTag_150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_150 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_152 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.alloc-correct
d_alloc'45'correct_154 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_154 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.base
d_base_160 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664
d_base_160 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.before-frontier-monotone
d_before'45'frontier'45'monotone_162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_before'45'frontier'45'monotone_162 ~v0
  = du_before'45'frontier'45'monotone_162
du_before'45'frontier'45'monotone_162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_before'45'frontier'45'monotone_162 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_before'45'frontier'45'monotone_7622
      v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.body-cap-eq
d_body'45'cap'45'eq_164 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_164 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.body-capacity
d_body'45'capacity_166 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_770 ->
  Integer
d_body'45'capacity_166 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'capacity_1482
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.body-correct
d_body'45'correct_168 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_770
d_body'45'correct_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'correct_1620
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.bump
d_bump_170 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924
d_bump_170 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1162
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_172 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1288
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_174 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1236
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.code-before
d_code'45'before_180 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_code'45'before_180 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_code'45'before_1612
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.code-ptr
d_code'45'ptr_182 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_182 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.decomposeClosureWF
d_decomposeClosureWF_184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668
d_decomposeClosureWF_184 ~v0 = du_decomposeClosureWF_184
du_decomposeClosureWF_184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668
du_decomposeClosureWF_184 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1738
      v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.decomposeInlWF
d_decomposeInlWF_186 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2024
d_decomposeInlWF_186 ~v0 = du_decomposeInlWF_186
du_decomposeInlWF_186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2024
du_decomposeInlWF_186 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeInlWF_2114
      v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.decomposeInrWF
d_decomposeInrWF_188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2068
d_decomposeInrWF_188 ~v0 = du_decomposeInrWF_188
du_decomposeInrWF_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2068
du_decomposeInrWF_188 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeInrWF_2156
      v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.decomposePairWF
d_decomposePairWF_190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892
d_decomposePairWF_190 ~v0 = du_decomposePairWF_190
du_decomposePairWF_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892
du_decomposePairWF_190 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1934
      v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.derive-mem-preserved
d_derive'45'mem'45'preserved_192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved_192 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.derive-mem-preserved-at
d_derive'45'mem'45'preserved'45'at_194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved'45'at_194 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.env-before
d_env'45'before_198 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_env'45'before_198 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'before_1610
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.env-ptr
d_env'45'ptr_202 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_202 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.env-valid
d_env'45'valid_204 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_env'45'valid_204 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'valid_1618
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.eval
d_eval_206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_eval_206 ~v0 = du_eval_206
du_eval_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_eval_206
  = coe MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval_22
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.evalᴰ
d_eval'7472'_208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval'7472'_208 ~v0 = du_eval'7472'_208
du_eval'7472'_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_eval'7472'_208
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval'7472'_28
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.execute
d_execute_210 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_770 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_210 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_execute_1500
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.final-alloc
d_final'45'alloc_212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_final'45'alloc_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_final'45'alloc_212 v8 v9
du_final'45'alloc_212 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_final'45'alloc_212 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1190
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.final-state
d_final'45'state_214 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_214 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1158
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.frame-preserved
d_frame'45'preserved_216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_216 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.frontier-slot-stable
d_frontier'45'slot'45'stable_218 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_218 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1246
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.heap-budget
d_heap'45'budget_220 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_heap'45'budget_220 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1284
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.heap-inv
d_heap'45'inv_222 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682
d_heap'45'inv_222 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.heap-monotone
d_heap'45'monotone_224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_heap'45'monotone_224 v8
du_heap'45'monotone_224 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_224 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1294
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.heap-preserved-of
d_heap'45'preserved'45'of_226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'preserved'45'of_226 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.inline-sv
d_inline'45'sv_234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_234 ~v0 = du_inline'45'sv_234
du_inline'45'sv_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_234 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_572
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.input-read
d_input'45'read_236 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1798 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'read_236 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.input-sv
d_input'45'sv_238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1798 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_input'45'sv_238 ~v0 = du_input'45'sv_238
du_input'45'sv_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1798 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_input'45'sv_238 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_input'45'sv_1830
      v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.inputPlace-transport
d_inputPlace'45'transport_240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1798 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1798
d_inputPlace'45'transport_240 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inputPlace'45'transport_6202
      (coe v0) v1 v2 v4 v5 v6 v7 v8 v9 v11 v12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.irresult-mem-preserved
d_irresult'45'mem'45'preserved_242 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irresult'45'mem'45'preserved_242 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.loc-mem-eq-from-regions
d_loc'45'mem'45'eq'45'from'45'regions_252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_LocInRegions_6264 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loc'45'mem'45'eq'45'from'45'regions_252 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mEnv
d_mEnv_254 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_254 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_mEnv_1616
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_256 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_256 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1290
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-heap-ref-written
d_max'45'heap'45'ref'45'written_258 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_max'45'heap'45'ref'45'written_258 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1286
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_260 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_260 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1292
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-slot-geq-final
d_max'45'slot'45'geq'45'final_262 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_262 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1238
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_264 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_264 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1240
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.max-slot-written
d_max'45'slot'45'written_266 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_max'45'slot'45'written_266 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1232
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mem-preserved-before
d_mem'45'preserved'45'before_268 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_268 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mem-preserved-compose
d_mem'45'preserved'45'compose_270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'compose_270 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mem-preserved-from-tnhw
d_mem'45'preserved'45'from'45'tnhw_272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'from'45'tnhw_272 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.mk-IRResultAWF-via-bump
d_mk'45'IRResultAWF'45'via'45'bump_274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698
d_mk'45'IRResultAWF'45'via'45'bump_274 ~v0
  = du_mk'45'IRResultAWF'45'via'45'bump_274
du_mk'45'IRResultAWF'45'via'45'bump_274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698
du_mk'45'IRResultAWF'45'via'45'bump_274 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
                                        v24
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_mk'45'IRResultAWF'45'via'45'bump_754
      v8 v10 v11 v16 v17 v20 v22 v23 v24
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.not-halted
d_not'45'halted_276 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_276 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.obs-budget
d_obs'45'budget_278 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_obs'45'budget_278 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1170
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.payload-read
d_payload'45'read_284 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1954 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'read_284 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.payload-sv
d_payload'45'sv_286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1954 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_payload'45'sv_286 ~v0 = du_payload'45'sv_286
du_payload'45'sv_286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1954 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_payload'45'sv_286 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_payload'45'sv_1986
      v3 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.place-rax
d_place'45'rax_288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_place'45'rax_288 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.place-sv
d_place'45'sv_290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_place'45'sv_290 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_place'45'sv_632
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.prim-sv
d_prim'45'sv_292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_292 ~v0 = du_prim'45'sv_292
du_prim'45'sv_292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_292 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_554
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.reclaim-alloc
d_reclaim'45'alloc_294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_reclaim'45'alloc_294 ~v0 = du_reclaim'45'alloc_294
du_reclaim'45'alloc_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_reclaim'45'alloc_294 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_reclaim'45'alloc_7302
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.reclaim-preserves-frontier
d_reclaim'45'preserves'45'frontier_296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_reclaim'45'preserves'45'frontier_296 ~v0
  = du_reclaim'45'preserves'45'frontier_296
du_reclaim'45'preserves'45'frontier_296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_reclaim'45'preserves'45'frontier_296 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_reclaim'45'preserves'45'frontier_7316
      v3 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.result-place
d_result'45'place_302 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618
d_result'45'place_302 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1172
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.scratch-bounded
d_scratch'45'bounded_304 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_304 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1258
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.scratch-budget
d_scratch'45'budget_306 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_scratch'45'budget_306 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1256
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.slot-monotone
d_slot'45'monotone_308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_slot'45'monotone_308 v8
du_slot'45'monotone_308 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_308 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1260
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8 v9
  = du_slot'45'stays'45'in'45'budget_310 v8 v9
du_slot'45'stays'45'in'45'budget_310 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_310 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1262
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1162
         (coe
            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.stack-budget
d_stack'45'budget_312 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_stack'45'budget_312 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1234
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.stack-inv
d_stack'45'inv_314 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674
d_stack'45'inv_314 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.sucLoc-before
d_sucLoc'45'before_316 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_316 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1614
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace
d_trace_318 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_trace_318 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1160
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-correct
d_trace'45'correct_320 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_320 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_322 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_322 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_324 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_324 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1188
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-preserves-halted
d_trace'45'preserves'45'halted_326 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_326 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_328 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_328 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1250
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_330 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_330 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1254
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-twf
d_trace'45'twf_332 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294
d_trace'45'twf_332 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1180
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-writes-above
d_trace'45'writes'45'above_334 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'writes'45'above_334 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1248
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.trace-writes-below
d_trace'45'writes'45'below_336 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'writes'45'below_336 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1252
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.transport-SumTag
d_transport'45'SumTag_338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_transport'45'SumTag_338 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.valid-primitive-wf
d_valid'45'primitive'45'wf_362 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_valid'45'primitive'45'wf_362 ~v0
  = du_valid'45'primitive'45'wf_362
du_valid'45'primitive'45'wf_362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
du_valid'45'primitive'45'wf_362 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'primitive'45'wf_604
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.valid-to-validWF-unit
d_valid'45'to'45'validWF'45'unit_366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_valid'45'to'45'validWF'45'unit_366 ~v0
  = du_valid'45'to'45'validWF'45'unit_366
du_valid'45'to'45'validWF'45'unit_366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
du_valid'45'to'45'validWF'45'unit_366 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'to'45'validWF'45'unit_2192
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-alloc-advance
d_validityWF'45'alloc'45'advance_374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'alloc'45'advance_374 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'alloc'45'advance_4430
      (coe v0) v1 v3 v4 v5 v6 v7 v8 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'frontier'45'advance_376 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4834
      (coe v0) v1 v3 v4 v5 v6 v7 v8 v10 v11 v12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-mem-only
d_validityWF'45'mem'45'only_378 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'mem'45'only_378 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'only_2208
      (coe v0) v1 v3 v4 v5 v7 v8 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'mem'45'preserved_380 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5730
      (coe v0) v1 v3 v4 v5 v7 v8 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-mem-preserved-excluding
d_validityWF'45'mem'45'preserved'45'excluding_382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'mem'45'preserved'45'excluding_382 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_validityWF'45'mem'45'preserved'45'excluding_6256
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-mem-preserved-in-regions
d_validityWF'45'mem'45'preserved'45'in'45'regions_384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
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
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'mem'45'preserved'45'in'45'regions_384 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_validityWF'45'mem'45'preserved'45'in'45'regions_7296
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-mem-preserved-in-regions-strong
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
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
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_386 v0
                                                                v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                v12 v13 v14 v15 v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6662
      (coe v0) v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v18 v19
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-reclaim
d_validityWF'45'reclaim_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'reclaim_388 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'reclaim_7400
      (coe v0) v1 v3 v4 v5 v6 v7 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-trace-preserves
d_validityWF'45'trace'45'preserves_390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'trace'45'preserves_390 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'trace'45'preserves_7540
      (coe v0) v1 v3 v4 v5 v6 v8 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'with'45'bf'45'transfer_392 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'with'45'bf'45'transfer_5326
      (coe v0) v1 v3 v4 v5 v6 v7 v8 v9 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-write-at-frontier
d_validityWF'45'write'45'at'45'frontier_394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'write'45'at'45'frontier_394 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'at'45'frontier_2668
      (coe v0) v1 v3 v4 v5 v7 v8 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-write-at-suc-frontier
d_validityWF'45'write'45'at'45'suc'45'frontier_396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'write'45'at'45'suc'45'frontier_396 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'at'45'suc'45'frontier_3108
      (coe v0) v1 v3 v4 v5 v7 v8 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-write-sv-at-frontier
d_validityWF'45'write'45'sv'45'at'45'frontier_398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'write'45'sv'45'at'45'frontier_398 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'sv'45'at'45'frontier_3548
      (coe v0) v1 v3 v4 v5 v7 v8 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.validityWF-write-sv-at-suc-frontier
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_400 v0 v1 v2
                                                         v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3988
      (coe v0) v1 v3 v4 v5 v7 v8 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.μ-validity-in-regions-stub
d_μ'45'validity'45'in'45'regions'45'stub_402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_μ'45'validity'45'in'45'regions'45'stub_402 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_μ'45'validity'45'in'45'regions'45'stub_6606
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ν-validity-in-regions-stub
d_ν'45'validity'45'in'45'regions'45'stub_404 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_ν'45'validity'45'in'45'regions'45'stub_404 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ν'45'validity'45'in'45'regions'45'stub_6630
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.BodyCorrect.body-cap-eq
d_body'45'cap'45'eq_408 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_408 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.BodyCorrect.body-capacity
d_body'45'capacity_410 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_770 ->
  Integer
d_body'45'capacity_410 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'capacity_1482
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.BodyCorrect.execute
d_execute_412 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_770 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_412 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_execute_1500
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.EnvType
d_EnvType_422 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_422 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_EnvType_1702
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.body
d_body_424 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_body_424 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body_1704
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.body-label
d_body'45'label_426 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_426 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'label_1708
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.code-ptr
d_code'45'ptr_428 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_428 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.env
d_env_430 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  AgdaAny
d_env_430 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env_1706 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.env-at
d_env'45'at_432 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1634
d_env'45'at_432 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'at_1712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_434 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_434 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.loc-mode
d_loc'45'mode_436 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  AgdaAny
d_loc'45'mode_436 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_loc'45'mode_1710
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_438 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_438 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1716
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.body-correct
d_body'45'correct_442 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_770
d_body'45'correct_442 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'correct_1620
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.code-before
d_code'45'before_444 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_code'45'before_444 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_code'45'before_1612
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.code-ptr
d_code'45'ptr_446 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_446 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.env-before
d_env'45'before_448 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_env'45'before_448 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'before_1610
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.env-ptr
d_env'45'ptr_450 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_450 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.env-valid
d_env'45'valid_452 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_env'45'valid_452 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'valid_1618
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.mEnv
d_mEnv_454 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_454 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_mEnv_1616
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.ClosureWellFormed.sucLoc-before
d_sucLoc'45'before_456 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1564 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_456 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1614
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_466 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_466 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1288
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.heap-budget
d_heap'45'budget_468 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682 ->
  Integer
d_heap'45'budget_468 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1284
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.heap-monotone
d_heap'45'monotone_470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_470 ~v0 = du_heap'45'monotone_470
du_heap'45'monotone_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_470 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1294
      v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_472 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_472 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1290
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-written
d_max'45'heap'45'ref'45'written_474 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682 ->
  Integer
d_max'45'heap'45'ref'45'written_474 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1286
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRHeapBudget.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_476 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_476 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1292
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.alloc-correct
d_alloc'45'correct_480 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_480 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.base
d_base_482 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664
d_base_482 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.bump
d_bump_484 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924
d_bump_484 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1162
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_486 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_486 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1288
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_488 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_488 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1236
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.final-alloc
d_final'45'alloc_490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_final'45'alloc_490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_final'45'alloc_490 v8 v9
du_final'45'alloc_490 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_final'45'alloc_490 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1190
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.final-state
d_final'45'state_492 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_492 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1158
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.frame-preserved
d_frame'45'preserved_494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_494 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.frontier-slot-stable
d_frontier'45'slot'45'stable_496 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_496 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1246
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.heap-budget
d_heap'45'budget_498 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_heap'45'budget_498 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1284
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.heap-inv
d_heap'45'inv_500 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_682
d_heap'45'inv_500 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.heap-monotone
d_heap'45'monotone_502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_heap'45'monotone_502 v8
du_heap'45'monotone_502 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_502 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1294
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_504 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_504 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1290
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-heap-ref-written
d_max'45'heap'45'ref'45'written_506 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_max'45'heap'45'ref'45'written_506 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1286
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_508 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_508 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1292
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1322
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-slot-geq-final
d_max'45'slot'45'geq'45'final_510 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_510 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1238
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_512 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_512 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1240
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.max-slot-written
d_max'45'slot'45'written_514 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_max'45'slot'45'written_514 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1232
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.mem-preserved-before
d_mem'45'preserved'45'before_516 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_516 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.not-halted
d_not'45'halted_518 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_518 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.obs-budget
d_obs'45'budget_520 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_obs'45'budget_520 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1170
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.result-place
d_result'45'place_522 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618
d_result'45'place_522 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1172
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.scratch-bounded
d_scratch'45'bounded_524 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_524 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1258
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.scratch-budget
d_scratch'45'budget_526 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_scratch'45'budget_526 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1256
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.slot-monotone
d_slot'45'monotone_528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_slot'45'monotone_528 v8
du_slot'45'monotone_528 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_528 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1260
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8 v9
  = du_slot'45'stays'45'in'45'budget_530 v8 v9
du_slot'45'stays'45'in'45'budget_530 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_530 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1262
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1162
         (coe
            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.stack-budget
d_stack'45'budget_532 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  Integer
d_stack'45'budget_532 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1234
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.stack-inv
d_stack'45'inv_534 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674
d_stack'45'inv_534 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace
d_trace_536 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_trace_536 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1160
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-correct
d_trace'45'correct_538 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_538 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_540 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_540 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_542 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_542 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1188
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-preserves-halted
d_trace'45'preserves'45'halted_544 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_544 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_546 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_546 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1250
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_548 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_548 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1254
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-twf
d_trace'45'twf_550 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294
d_trace'45'twf_550 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1180
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1318
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-writes-above
d_trace'45'writes'45'above_552 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'writes'45'above_552 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1248
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultAWF.trace-writes-below
d_trace'45'writes'45'below_554 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_698 ->
  AgdaAny
d_trace'45'writes'45'below_554 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1252
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1320
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.alloc-correct
d_alloc'45'correct_558 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_558 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.bump
d_bump_560 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924
d_bump_560 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1162
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.final-alloc
d_final'45'alloc_562 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_final'45'alloc_562 ~v0 = du_final'45'alloc_562
du_final'45'alloc_562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_final'45'alloc_562 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1190
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.final-state
d_final'45'state_564 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_564 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1158
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.frame-preserved
d_frame'45'preserved_566 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_566 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.mem-preserved-before
d_mem'45'preserved'45'before_568 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_568 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.not-halted
d_not'45'halted_570 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_570 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.obs-budget
d_obs'45'budget_572 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  Integer
d_obs'45'budget_572 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1170
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.result-place
d_result'45'place_574 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618
d_result'45'place_574 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1172
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace
d_trace_576 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_trace_576 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1160
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-correct
d_trace'45'correct_578 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_578 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_580 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_580 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_582 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_582 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1188
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-preserves-halted
d_trace'45'preserves'45'halted_584 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_584 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRResultBase.trace-twf
d_trace'45'twf_586 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294
d_trace'45'twf_586 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1180
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_590 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_590 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1236
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.frontier-slot-stable
d_frontier'45'slot'45'stable_592 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_592 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1246
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.max-slot-geq-final
d_max'45'slot'45'geq'45'final_594 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_594 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1238
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_596 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_596 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1240
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.max-slot-written
d_max'45'slot'45'written_598 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  Integer
d_max'45'slot'45'written_598 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1232
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.scratch-bounded
d_scratch'45'bounded_600 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_600 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1258
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.scratch-budget
d_scratch'45'budget_602 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  Integer
d_scratch'45'budget_602 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1256
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.slot-monotone
d_slot'45'monotone_604 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_604 ~v0 = du_slot'45'monotone_604
du_slot'45'monotone_604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_604 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1260
      v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_606 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_606 ~v0
  = du_slot'45'stays'45'in'45'budget_606
du_slot'45'stays'45'in'45'budget_606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_606 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1262
      v1 v2 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.stack-budget
d_stack'45'budget_608 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  Integer
d_stack'45'budget_608 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1234
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_610 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_610 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1250
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_612 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_612 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1254
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.trace-writes-above
d_trace'45'writes'45'above_614 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  AgdaAny
d_trace'45'writes'45'above_614 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1248
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.IRStackBudget.trace-writes-below
d_trace'45'writes'45'below_616 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_674 ->
  AgdaAny
d_trace'45'writes'45'below_616 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1252
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF.a
d_a_620 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2024 ->
  AgdaAny
d_a_620 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_a_2046 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF.payload
d_payload_622 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2024 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1954
d_payload_622 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_payload_2050
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF.sucLoc-before
d_sucLoc'45'before_624 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2024 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_624 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_2048
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InlValidWF.v-is-inl
d_v'45'is'45'inl_626 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2024 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_626 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF.b
d_b_644 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2068 ->
  AgdaAny
d_b_644 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_b_2090 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF.payload
d_payload_646 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2068 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1954
d_payload_646 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_payload_2094
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF.sucLoc-before
d_sucLoc'45'before_648 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2068 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_648 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_2092
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.InrValidWF.v-is-inr
d_v'45'is'45'inr_650 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2068 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_650 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PairValidWF.fst-cell
d_fst'45'cell_664 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584
d_fst'45'cell_664 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1914
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PairValidWF.snd-cell
d_snd'45'cell_666 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584
d_snd'45'cell_666 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1916
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ClosureWellFormedDef.PairValidWF.sucLoc-before
d_sucLoc'45'before_668 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_668 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1912
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.AllSlotStable
d_AllSlotStable_724 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_AllSlotStable_724 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BeforeFrontier
d_BeforeFrontier_726 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlockAt
d_BlockAt_728 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockAt_728 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlockRuns
d_BlockRuns_730 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlocksAt
d_BlocksAt_734 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_BlocksAt_734 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CallPost
d_CallPost_736 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun
d_CalleeRun_738 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRuns
d_CalleeRuns_742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_CalleeRuns_742 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CellAt
d_CellAt_744 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CoalgRuns
d_CoalgRuns_746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_CoalgRuns_746 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.EnvAt
d_EnvAt_748 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState
d_FlatState_750 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatSteps
d_FlatSteps_754 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatSteps-++
d_FlatSteps'45''43''43'_756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45''43''43'_756 ~v0 ~v1 = du_FlatSteps'45''43''43'_756
du_FlatSteps'45''43''43'_756 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45''43''43'_756 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1138
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatSteps-prefix
d_FlatSteps'45'prefix_758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45'prefix_758 ~v0 ~v1 = du_FlatSteps'45'prefix_758
du_FlatSteps'45'prefix_758 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45'prefix_758 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'prefix_966
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatSteps-reloc
d_FlatSteps'45'reloc_760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45'reloc_760 ~v0 ~v1 = du_FlatSteps'45'reloc_760
du_FlatSteps'45'reloc_760 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45'reloc_760 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'reloc_1008
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlinkView
d_FlinkView_762 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.IRObsCorrectF
d_IRObsCorrectF_764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_764 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.InlineRep
d_InlineRep_766 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.InputAt
d_InputAt_768 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.InstrWF
d_InstrWF_770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_InstrWF_770 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.MachineRefinesObsF
d_MachineRefinesObsF_772 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ProgFree
d_ProgFree_776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_ProgFree_776 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.Readable
d_Readable_778 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ResultPlace
d_ResultPlace_780 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.Shifted
d_Shifted_782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Shifted_782 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.SpanAt
d_SpanAt_784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_SpanAt_784 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.Straight
d_Straight_786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_Straight_786 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.StraightStep
d_StraightStep_788 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_StraightStep_788 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValidAtWF
d_ValidAtWF_790 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized
d_ValueRealized_792 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.blocks
d_blocks_802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_802 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_3376
      (coe v0) v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.callView
d_callView_804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178
d_callView_804 ~v0 v1 = du_callView_804 v1
du_callView_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178
du_callView_804 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1196 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.cata-correct
d_cata'45'correct_808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660
d_cata'45'correct_808 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cata'45'correct_3974
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.chain-events
d_chain'45'events_814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_chain'45'events_814 ~v0 v1 = du_chain'45'events_814 v1
du_chain'45'events_814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_chain'45'events_814 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_578
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.chain-events-++
d_chain'45'events'45''43''43'_816 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_816 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.chain-events-nil
d_chain'45'events'45'nil_818 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_818 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.chain-events-subst-start
d_chain'45'events'45'subst'45'start_820 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_820 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.decomposeClosureWF
d_decomposeClosureWF_826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668
d_decomposeClosureWF_826 ~v0 ~v1 = du_decomposeClosureWF_826
du_decomposeClosureWF_826 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668
du_decomposeClosureWF_826 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1738
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.decomposePairWF
d_decomposePairWF_828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892
d_decomposePairWF_828 ~v0 ~v1 = du_decomposePairWF_828
du_decomposePairWF_828 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892
du_decomposePairWF_828 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1934
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-branch
d_do'45'branch_830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_830 ~v0 v1 = du_do'45'branch_830 v1
du_do'45'branch_830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch_830 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_766 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-branch-at
d_do'45'branch'45'at_832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch'45'at_832 ~v0 ~v1 = du_do'45'branch'45'at_832
du_do'45'branch'45'at_832 ::
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch'45'at_832
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'branch'45'at_758
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call
d_do'45'call_834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_834 ~v0 v1 = du_do'45'call_834 v1
du_do'45'call_834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call_834 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1168 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-at
d_do'45'call'45'at_836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_836 ~v0 v1 = du_do'45'call'45'at_836 v1
du_do'45'call'45'at_836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'at_836 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1112 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-code
d_do'45'call'45'code_838 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'code_838 ~v0 v1 = du_do'45'call'45'code_838 v1
du_do'45'call'45'code_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'code_838 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'code_1120
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-code-prefix
d_do'45'call'45'code'45'prefix_840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'code'45'prefix_840 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-prefix
d_do'45'call'45'prefix_842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'prefix_842 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-sv
d_do'45'call'45'sv_844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'sv_844 ~v0 v1 = du_do'45'call'45'sv_844 v1
du_do'45'call'45'sv_844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'sv_844 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'sv_1144 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-call-sv-prefix
d_do'45'call'45'sv'45'prefix_846 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'sv'45'prefix_846 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-jump
d_do'45'jump_848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_848 ~v0 ~v1 = du_do'45'jump_848
du_do'45'jump_848 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_848
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_750
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret
d_do'45'ret_850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_850 ~v0 ~v1 = du_do'45'ret_850
du_do'45'ret_850 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_850
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_968
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-alloc
d_do'45'ret'45'alloc_852 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_852 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_854 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_856 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_858 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_860 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-save-closure
d_do'45'save'45'closure_862 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'save'45'closure_862 ~v0 ~v1 = du_do'45'save'45'closure_862
du_do'45'save'45'closure_862 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'save'45'closure_862
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1326
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.do-thunk
d_do'45'thunk_864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_864 ~v0 v1 = du_do'45'thunk_864 v1
du_do'45'thunk_864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_864 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1102 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.emitted
d_emitted_866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_emitted_866 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_3364
      (coe v0) v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.enter-call
d_enter'45'call_868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_enter'45'call_868 ~v0 v1 = du_enter'45'call_868 v1
du_enter'45'call_868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_enter'45'call_868 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_788 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.enter-frame
d_enter'45'frame_870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_enter'45'frame_870 ~v0 v1 = du_enter'45'frame_870 v1
du_enter'45'frame_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_enter'45'frame_870 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'frame_782 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.entry-flat
d_entry'45'flat_872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_entry'45'flat_872 ~v0 v1 v2 v3 v4
  = du_entry'45'flat_872 v1 v2 v3 v4
du_entry'45'flat_872 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_entry'45'flat_872 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v1)
      (coe v2) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.eval
d_eval_878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_eval_878 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Eval.d_eval_12 (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_158 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.evalᴰ
d_eval'7472'_880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval'7472'_880 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_158 (coe v0))
      (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.event-of
d_event'45'of_882 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_event'45'of_882 ~v0 v1 = du_event'45'of_882 v1
du_event'45'of_882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_event'45'of_882 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_event'45'of_432 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract
d_exec'45'abstract_884 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_884 ~v0 v1 = du_exec'45'abstract_884 v1
du_exec'45'abstract_884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_884 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2954
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-load-indirect-output
d_exec'45'abstract'45'load'45'indirect'45'output_886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'output_886 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-load-indirect-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_888
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-load-indirect-suc-output
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_890 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_890
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-load-indirect-suc-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_892
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_894 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-halted-WF
d_exec'45'abstract'45'preserves'45'halted'45'WF_896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted'45'WF_896 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-heap-ref
d_exec'45'abstract'45'preserves'45'heap'45'ref_898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heap'45'ref_898 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_900 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_902 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_902 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat
d_exec'45'flat_904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_904 ~v0 v1 = du_exec'45'flat_904 v1
du_exec'45'flat_904 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_exec'45'flat_904 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3372 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-halted
d_exec'45'flat'45'halted_906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_906 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-invariant
d_exec'45'flat'45'invariant_908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_908 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-keeps-next-slot
d_exec'45'flat'45'keeps'45'next'45'slot_910 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'keeps'45'next'45'slot_910 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-offend
d_exec'45'flat'45'offend_912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_912 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-reloc
d_exec'45'flat'45'reloc_914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'flat'45'reloc_914 ~v0 v1
  = du_exec'45'flat'45'reloc_914 v1
du_exec'45'flat'45'reloc_914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'flat'45'reloc_914 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'flat'45'reloc_3422
      (coe v0) v1 v2 v3 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-step
d_exec'45'flat'45'step_916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_916 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-steps
d_exec'45'flat'45'steps_918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_918 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-stop
d_exec'45'flat'45'stop_920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'stop_920 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_922 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_922 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-sigop-halts
d_exec'45'sigop'45'halts_924 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_924 ~v0 ~v1
  = du_exec'45'sigop'45'halts_924
du_exec'45'sigop'45'halts_924 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts_924 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_2854
      v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_926 ~v0 ~v1
  = du_exec'45'sigop'45'halts'45'of_926
du_exec'45'sigop'45'halts'45'of_926 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts'45'of_926 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_2848
      v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_928 ~v0 v1
  = du_exec'45'sigop'45'output'45'of_928 v1
du_exec'45'sigop'45'output'45'of_928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_928 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2828
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-trace-halted
d_exec'45'trace'45'halted_930 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_930 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_932 ~v0 ~v1
  = du_exec'45'trace'45'is'45'flat_932
du_exec'45'trace'45'is'45'flat_932 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_932 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'trace'45'is'45'flat_4198
      v0 v1 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.falloc
d_falloc_934 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_934 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fclosure
d_fclosure_936 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_936 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch
d_fetch_938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
d_fetch_938 ~v0 ~v1 = du_fetch_938
du_fetch_938 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
du_fetch_938 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_214
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-++-left
d_fetch'45''43''43''45'left_940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'left_940 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-++-right
d_fetch'45''43''43''45'right_942 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'right_942 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-All
d_fetch'45'All_944 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_944 ~v0 ~v1 = du_fetch'45'All_944
du_fetch'45'All_944 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_fetch'45'All_944 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_3874 v1 v2 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-Straight
d_fetch'45'Straight_946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_946 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fetch-dispatch
d_fetch'45'dispatch_948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fetch'45'dispatch_948 ~v0 v1 = du_fetch'45'dispatch_948 v1
du_fetch'45'dispatch_948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fetch'45'dispatch_948 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fetch'45'dispatch_3376
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-label
d_find'45'label_950 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_950 ~v0 v1 = du_find'45'label_950 v1
du_find'45'label_950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_950 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-label-lands
d_find'45'label'45'lands_952 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_952 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-label-sound
d_find'45'label'45'sound_954 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_954 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-thunk
d_find'45'thunk_956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_956 ~v0 v1 = du_find'45'thunk_956 v1
du_find'45'thunk_956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_956 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_208 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.find-thunk-sound
d_find'45'thunk'45'sound_958 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_958 ~v0 v1
  = du_find'45'thunk'45'sound_958 v1
du_find'45'thunk'45'sound_958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'sound_958 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'thunk'45'sound_724
      (coe v0) v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-at
d_fl'45'at_960 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_960 ~v0 v1 = du_fl'45'at_960 v1
du_fl'45'at_960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'at_960 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'at_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-at-++-miss
d_fl'45'at'45''43''43''45'miss_962 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'at'45''43''43''45'miss_962 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-go
d_fl'45'go_964 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_964 ~v0 v1 = du_fl'45'go_964 v1
du_fl'45'go_964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'go_964 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-go-++-miss
d_fl'45'go'45''43''43''45'miss_966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45''43''43''45'miss_966 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-go-lands
d_fl'45'go'45'lands_968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_968 ~v0 v1 = du_fl'45'go'45'lands_968 v1
du_fl'45'go'45'lands_968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_968 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'lands_3658
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-go-sound
d_fl'45'go'45'sound_970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_970 ~v0 v1 = du_fl'45'go'45'sound_970 v1
du_fl'45'go'45'sound_970 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_970 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'sound_604
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-label-match
d_fl'45'label'45'match_972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_972 ~v0 v1 = du_fl'45'label'45'match_972 v1
du_fl'45'label'45'match_972 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'label'45'match_972 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fl-match-++-miss
d_fl'45'match'45''43''43''45'miss_974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'match'45''43''43''45'miss_974 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-events
d_flat'45'events_976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'events_976 ~v0 v1 = du_flat'45'events_976 v1
du_flat'45'events_976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_flat'45'events_976 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_438 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-events-[]
d_flat'45'events'45''91''93'_978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_978 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-exec-instr
d_flat'45'exec'45'instr_980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_980 ~v0 v1
  = du_flat'45'exec'45'instr_980 v1
du_flat'45'exec'45'instr_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_980 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-exec-instr-prefix
d_flat'45'exec'45'instr'45'prefix_982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prefix_982 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-exec-instr-prog-irrelevant
d_flat'45'exec'45'instr'45'prog'45'irrelevant_984 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prog'45'irrelevant_984 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-halt
d_flat'45'halt_986 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'halt_986 ~v0 ~v1 = du_flat'45'halt_986
du_flat'45'halt_986 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'halt_986
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'halt_1108
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-read-at
d_flat'45'read'45'at_988 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'at_988 ~v0 ~v1 = du_flat'45'read'45'at_988
du_flat'45'read'45'at_988 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'at_988
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'at_110
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-read-tag
d_flat'45'read'45'tag_990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_990 ~v0 ~v1 = du_flat'45'read'45'tag_990
du_flat'45'read'45'tag_990 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_990
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-run
d_flat'45'run_992 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'run_992 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3372 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v4)
         (coe v5) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-run-keeps-next-slot
d_flat'45'run'45'keeps'45'next'45'slot_994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'run'45'keeps'45'next'45'slot_994 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-step-frame
d_flat'45'step'45'frame_996 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'frame_996 ~v0 v1
  = du_flat'45'step'45'frame_996 v1
du_flat'45'step'45'frame_996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'frame_996 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'frame_960
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flat-step-straight
d_flat'45'step'45'straight_998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'straight_998 ~v0 v1
  = du_flat'45'step'45'straight_998 v1
du_flat'45'step'45'straight_998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'straight_998 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flink
d_flink_1000 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1000 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flink-do-branch
d_flink'45'do'45'branch_1002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch_1002 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flink-do-jump
d_flink'45'do'45'jump_1004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'jump_1004 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flink-do-ret
d_flink'45'do'45'ret_1006 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'ret_1006 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.flinkView
d_flinkView_1008 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3202
d_flinkView_1008 ~v0 ~v1 = du_flinkView_1008
du_flinkView_1008 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3202
du_flinkView_1008
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flinkView_3222
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.floc
d_floc_1010 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_1010 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.forced
d_forced_1012 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_forced_1012 ~v0 ~v1 = du_forced_1012
du_forced_1012 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_forced_1012
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_4188
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fpc
d_fpc_1014 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1014 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.fret
d_fret_1016 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1016 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.frontier-monotone
d_frontier'45'monotone_1018 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_frontier'45'monotone_1018 ~v0 ~v1 = du_frontier'45'monotone_1018
du_frontier'45'monotone_1018 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_frontier'45'monotone_1018 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-at
d_ft'45'at_1020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'at_1020 ~v0 v1 = du_ft'45'at_1020 v1
du_ft'45'at_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'at_1020 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'at_174 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-at-++-miss
d_ft'45'at'45''43''43''45'miss_1022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45''43''43''45'miss_1022 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-go
d_ft'45'go_1024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'go_1024 ~v0 v1 = du_ft'45'go_1024 v1
du_ft'45'go_1024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'go_1024 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_172 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-go-++-miss
d_ft'45'go'45''43''43''45'miss_1026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45''43''43''45'miss_1026 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-go-sound
d_ft'45'go'45'sound_1028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_1028 ~v0 v1 = du_ft'45'go'45'sound_1028 v1
du_ft'45'go'45'sound_1028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_1028 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_ft'45'go'45'sound_496
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-match
d_ft'45'match_1030 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'match_1030 ~v0 v1 = du_ft'45'match_1030 v1
du_ft'45'match_1030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'match_1030 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_176 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ft-match-++-miss
d_ft'45'match'45''43''43''45'miss_1032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45''43''43''45'miss_1032 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.grow-frame
d_grow'45'frame_1040 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_grow'45'frame_1040 ~v0 v1 = du_grow'45'frame_1040 v1
du_grow'45'frame_1040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_grow'45'frame_1040 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_grow'45'frame_1096 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.inline-sv
d_inline'45'sv_1048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_1048 ~v0 ~v1 = du_inline'45'sv_1048
du_inline'45'sv_1048 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_1048 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_572
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ir-stable
d_ir'45'stable_1050 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_1050 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'stable_520
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_1052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_1052 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_876
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.just-injℕ
d_just'45'injℕ_1054 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_1054 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.lab-eq
d_lab'45'eq_1056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_1056 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.label-of?
d_label'45'of'63'_1058 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_1058 ~v0 ~v1 = du_label'45'of'63'_1058
du_label'45'of'63'_1058 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_1058
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_122
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.label-of?-sound
d_label'45'of'63''45'sound_1060 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_1060 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame
d_leave'45'frame_1062 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame_1062 ~v0 ~v1 = du_leave'45'frame_1062
du_leave'45'frame_1062 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame_1062
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_804
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-aux
d_leave'45'frame'45'aux_1064 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame'45'aux_1064 ~v0 ~v1
  = du_leave'45'frame'45'aux_1064
du_leave'45'frame'45'aux_1064 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame'45'aux_1064
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_792
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-block-size
d_leave'45'frame'45'block'45'size_1066 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_1066 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_1068 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_1068 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_1070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_1070 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_1072 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_1072 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_1074 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_1074 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_1076 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_1076 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_1078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_1078 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.load-indirect-suc-twf
d_load'45'indirect'45'suc'45'twf_1080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'twf_1080 ~v0 ~v1
  = du_load'45'indirect'45'suc'45'twf_1080
du_load'45'indirect'45'suc'45'twf_1080 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'twf_1080 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'suc'45'twf_8284
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.load-indirect-twf
d_load'45'indirect'45'twf_1082 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'twf_1082 ~v0 ~v1
  = du_load'45'indirect'45'twf_1082
du_load'45'indirect'45'twf_1082 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'twf_1082 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'twf_8266
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.mkFlat
d_mkFlat_1084 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_mkFlat_1084 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v0)
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.prim-sv
d_prim'45'sv_1088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_1088 ~v0 ~v1 = du_prim'45'sv_1088
du_prim'45'sv_1088 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_1088 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_554
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_1090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_1090 ~v0 v1
  = du_pure'45'sigop'45'out'45'aux_1090 v1
du_pure'45'sigop'45'out'45'aux_1090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'aux_1090 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2792
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_1092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_1092 ~v0 v1
  = du_pure'45'sigop'45'out'45'val_1092 v1
du_pure'45'sigop'45'out'45'val_1092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_1092 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2776
      (coe v0) v2 v3 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.pure-sigop-output
d_pure'45'sigop'45'output_1094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_1094 ~v0 v1
  = du_pure'45'sigop'45'output_1094 v1
du_pure'45'sigop'45'output_1094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'output_1094 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_2770
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readLoc
d_readLoc_1102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1102 ~v0 ~v1 = du_readLoc_1102
du_readLoc_1102 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1102
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_1104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_1104 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readReg-typed
d_readReg'45'typed_1106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_1106 ~v0 ~v1 = du_readReg'45'typed_1106
du_readReg'45'typed_1106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_1106
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2728
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readTyped
d_readTyped_1108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_readTyped_1108 ~v0 ~v1 = du_readTyped_1108
du_readTyped_1108 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_readTyped_1108
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2734
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readTyped-adequate
d_readTyped'45'adequate_1110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_854 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'adequate_1110 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.readable?
d_readable'63'_1112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_854
d_readable'63'_1112 ~v0 ~v1 = du_readable'63'_1112
du_readable'63'_1112 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_854
du_readable'63'_1112
  = coe
      MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'63'_868
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.reg-write-readLoc
d_reg'45'write'45'readLoc_1116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'write'45'readLoc_1116 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.reloc-fetch
d_reloc'45'fetch_1118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'fetch_1118 ~v0 v1 = du_reloc'45'fetch_1118 v1
du_reloc'45'fetch_1118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'fetch_1118 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'fetch_3466 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.reloc-step
d_reloc'45'step_1120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'step_1120 ~v0 v1 = du_reloc'45'step_1120 v1
du_reloc'45'step_1120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'step_1120 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'step_3444 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shift
d_shift_1126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_shift_1126 ~v0 ~v1 = du_shift_1126
du_shift_1126 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_shift_1126
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shift_3128
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shift-loc
d_shift'45'loc_1128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_1128 ~v0 v1 = du_shift'45'loc_1128 v1
du_shift'45'loc_1128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_1128 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shift'45'loc_4040 (coe v0) v1
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-branch
d_shifted'45'branch_1130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'branch_1130 ~v0 ~v1 = du_shifted'45'branch_1130
du_shifted'45'branch_1130 ::
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
du_shifted'45'branch_1130 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'branch_1642 v1 v4
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-call-at
d_shifted'45'call'45'at_1132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'at_1132 ~v0 ~v1
  = du_shifted'45'call'45'at_1132
du_shifted'45'call'45'at_1132 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'at_1132 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'at_1780 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-call-closure
d_shifted'45'call'45'closure_1134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'closure_1134 ~v0 v1
  = du_shifted'45'call'45'closure_1134 v1
du_shifted'45'call'45'closure_1134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'closure_1134 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'closure_1996
      (coe v0) v3 v4 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-call-code
d_shifted'45'call'45'code_1136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'code_1136 ~v0 v1
  = du_shifted'45'call'45'code_1136 v1
du_shifted'45'call'45'code_1136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'code_1136 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'code_1828
      (coe v0) v2 v4 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-call-sv
d_shifted'45'call'45'sv_1138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'sv_1138 ~v0 v1
  = du_shifted'45'call'45'sv_1138 v1
du_shifted'45'call'45'sv_1138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'sv_1138 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'sv_1910
      (coe v0) v2 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-eq
d_shifted'45'eq_1140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shifted'45'eq_1140 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-frame
d_shifted'45'frame_1142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'frame_1142 ~v0 ~v1 = du_shifted'45'frame_1142
du_shifted'45'frame_1142 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'frame_1142 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'frame_1680 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-halt
d_shifted'45'halt_1144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'halt_1144 ~v0 ~v1 = du_shifted'45'halt_1144
du_shifted'45'halt_1144 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'halt_1144 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'halt_1746 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-instr
d_shifted'45'instr_1146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'instr_1146 ~v0 v1 = du_shifted'45'instr_1146 v1
du_shifted'45'instr_1146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'instr_1146 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'instr_2036
      (coe v0) v2 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-jump
d_shifted'45'jump_1148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'jump_1148 ~v0 ~v1 = du_shifted'45'jump_1148
du_shifted'45'jump_1148 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'jump_1148 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'jump_1584 v2 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-label
d_shifted'45'label_1150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'label_1150 ~v0 ~v1 = du_shifted'45'label_1150
du_shifted'45'label_1150 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'label_1150 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'label_1442 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-ret
d_shifted'45'ret_1152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret_1152 ~v0 ~v1 = du_shifted'45'ret_1152
du_shifted'45'ret_1152 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret_1152 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret_1560 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-ret-aux
d_shifted'45'ret'45'aux_1154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret'45'aux_1154 ~v0 ~v1
  = du_shifted'45'ret'45'aux_1154
du_shifted'45'ret'45'aux_1154 ::
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret'45'aux_1154 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret'45'aux_1508 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-save-closure
d_shifted'45'save'45'closure_1156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'save'45'closure_1156 ~v0 ~v1
  = du_shifted'45'save'45'closure_1156
du_shifted'45'save'45'closure_1156 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'save'45'closure_1156 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'save'45'closure_1718
      v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-shift
d_shifted'45'shift_1158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'shift_1158 ~v0 ~v1 = du_shifted'45'shift_1158
du_shifted'45'shift_1158 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'shift_1158 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'shift_3142
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-straight
d_shifted'45'straight_1160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'straight_1160 ~v0 ~v1 = du_shifted'45'straight_1160
du_shifted'45'straight_1160 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'straight_1160 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'straight_1406 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.shifted-thunk
d_shifted'45'thunk_1162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'thunk_1162 ~v0 ~v1 = du_shifted'45'thunk_1162
du_shifted'45'thunk_1162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'thunk_1162 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'thunk_1470 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.step-dispatch
d_step'45'dispatch_1164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_step'45'dispatch_1164 ~v0 v1 = du_step'45'dispatch_1164 v1
du_step'45'dispatch_1164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_step'45'dispatch_1164 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_step'45'dispatch_3374 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_1166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_1166 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_1168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_1168 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.sv-is-zero
d_sv'45'is'45'zero_1170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_1170 ~v0 ~v1 = du_sv'45'is'45'zero_1170
du_sv'45'is'45'zero_1170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_1170
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.tag-zf
d_tag'45'zf_1172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_1172 ~v0 ~v1 = du_tag'45'zf_1172
du_tag'45'zf_1172 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_1172
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.thunk-of?
d_thunk'45'of'63'_1174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_1174 ~v0 ~v1 = du_thunk'45'of'63'_1174
du_thunk'45'of'63'_1174 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_1174
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63'_168
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.thunk-of?-sound
d_thunk'45'of'63''45'sound_1176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_1176 ~v0 ~v1
  = du_thunk'45'of'63''45'sound_1176
du_thunk'45'of'63''45'sound_1176 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_1176 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63''45'sound_476
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.valid-primitive-wf
d_valid'45'primitive'45'wf_1194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_valid'45'primitive'45'wf_1194 ~v0 ~v1
  = du_valid'45'primitive'45'wf_1194
du_valid'45'primitive'45'wf_1194 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
du_valid'45'primitive'45'wf_1194 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'primitive'45'wf_604
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_1200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'frontier'45'advance_1200 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4834
      (coe v0) (coe v1) v3 v4 v5 v6 v7 v8 v10 v11 v12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_1202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'mem'45'preserved_1202 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                      v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5730
      (coe v0) (coe v1) v3 v4 v5 v7 v8 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_1204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'with'45'bf'45'transfer_1204 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'with'45'bf'45'transfer_5326
      (coe v0) (coe v1) v3 v4 v5 v6 v7 v8 v9 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.vr-mem-pres
d_vr'45'mem'45'pres_1206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vr'45'mem'45'pres_1206 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.μ-layer-iso
d_μ'45'layer'45'iso_1208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_μ'45'layer'45'iso_1208 ~v0 = du_μ'45'layer'45'iso_1208
du_μ'45'layer'45'iso_1208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
du_μ'45'layer'45'iso_1208 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_μ'45'layer'45'iso_3346
      v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.≡ᵇ-true
d_'8801''7495''45'true_1210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_1210 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlockRuns.closures
d_closures_1222 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closures_1222 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_closures_3926
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.BlockRuns.coalgs
d_coalgs_1224 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coalgs_1224 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_3928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.bf-mono
d_bf'45'mono_1234 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_bf'45'mono_1234 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3836
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.cont-alloc
d_cont'45'alloc_1236 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_1236 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3802
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.events
d_events_1238 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_1238 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.frame-pres
d_frame'45'pres_1240 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1240 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.live
d_live_1242 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1242 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.mem-pres
d_mem'45'pres_1244 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_1244 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.no-link
d_no'45'link_1246 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1246 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.no-ret
d_no'45'ret_1248 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1248 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.out-mode
d_out'45'mode_1250 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1250 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3800
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.place
d_place_1252 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618
d_place_1252 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3814
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.returned
d_returned_1254 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_1254 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.run
d_run_1256 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_1256 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3804
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.settle
d_settle_1258 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1258 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3798
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.CalleeRun.steps
d_steps_1260 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  Integer
d_steps_1260 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3796
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.EnvType
d_EnvType_1270 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_1270 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_EnvType_1702
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.body
d_body_1272 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_body_1272 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body_1704
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.body-label
d_body'45'label_1274 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_1274 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'label_1708
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.code-ptr
d_code'45'ptr_1276 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1276 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.env
d_env_1278 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  AgdaAny
d_env_1278 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env_1706 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.env-at
d_env'45'at_1280 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1634
d_env'45'at_1280 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'at_1712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_1282 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_1282 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.loc-mode
d_loc'45'mode_1284 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  AgdaAny
d_loc'45'mode_1284 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_loc'45'mode_1710
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_1286 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_1286 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1716
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.falloc
d_falloc_1296 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_1296 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.fclosure
d_fclosure_1298 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1298 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.flink
d_flink_1300 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1300 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.floc
d_floc_1302 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_1302 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.fpc
d_fpc_1304 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1304 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.FlatState.fret
d_fret_1306 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1306 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.MachineRefinesObsF.traces-agree
d_traces'45'agree_1338 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1338 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.MachineRefinesObsF.value-realized
d_value'45'realized_1340 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488
d_value'45'realized_1340 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3690
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.PairValidWF.fst-cell
d_fst'45'cell_1344 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584
d_fst'45'cell_1344 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1914
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.PairValidWF.snd-cell
d_snd'45'cell_1346 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584
d_snd'45'cell_1346 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1916
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.PairValidWF.sucLoc-before
d_sucLoc'45'before_1348 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_1348 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1912
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.at-end
d_at'45'end_1398 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1398 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.bf-mono
d_bf'45'mono_1400 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_bf'45'mono_1400 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3588
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.cont-alloc
d_cont'45'alloc_1402 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_1402 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3558
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.frame-pres
d_frame'45'pres_1404 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1404 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.heap-pres
d_heap'45'pres_1406 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_1406 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.live
d_live_1408 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1408 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.no-link
d_no'45'link_1410 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1410 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.no-ret
d_no'45'ret_1412 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1412 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.out-mode
d_out'45'mode_1414 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1414 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3556
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.place
d_place_1416 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618
d_place_1416 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3570
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.run
d_run_1418 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_1418 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3560
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.settle
d_settle_1420 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1420 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3554
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.stack-pres
d_stack'45'pres_1422 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_1422 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Core.ValueRealized.steps
d_steps_1424 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  Integer
d_steps_1424 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3552
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_1428 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SMPrimitives.instr-writes-slot
d_instr'45'writes'45'slot_1430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe Integer
d_instr'45'writes'45'slot_1430 ~v0
  = du_instr'45'writes'45'slot_1430
du_instr'45'writes'45'slot_1430 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe Integer
du_instr'45'writes'45'slot_1430
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_instr'45'writes'45'slot_666
-- Once.CCC.Codegen.IRObsCorrect.Machine._._+_
d__'43'__1512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Integer
d__'43'__1512 ~v0 = du__'43'__1512
du__'43'__1512 :: Integer -> Integer -> Integer
du__'43'__1512 = coe addInt
-- Once.CCC.Codegen.IRObsCorrect.Machine._._++_
d__'43''43'__1514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d__'43''43'__1514 ~v0 = du__'43''43'__1514
du__'43''43'__1514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'43''43'__1514 v0 v1 v2 v3
  = coe MAlonzo.Code.Data.List.Base.du__'43''43'__32 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._._<_
d__'60'__1518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> ()
d__'60'__1518 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._._×_
d__'215'__1520 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'__1520 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._._-_
d__'45'__1526 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> Integer
d__'45'__1526 ~v0 = du__'45'__1526
du__'45'__1526 :: Integer -> Integer -> Integer
du__'45'__1526 = coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
-- Once.CCC.Codegen.IRObsCorrect.Machine._._≟HL_
d__'8799'HL__1528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'HL__1528 ~v0 = du__'8799'HL__1528
du__'8799'HL__1528 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'HL__1528
  = coe MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80
-- Once.CCC.Codegen.IRObsCorrect.Machine._._≡_
d__'8801'__1530 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._._≢_
d__'8802'__1532 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> ()
d__'8802'__1532 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._._≤_
d__'8804'__1534 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.++-assoc
d_'43''43''45'assoc_1536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'assoc_1536 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.++⁺
d_'43''43''8314'_1538 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_'43''43''8314'_1538 ~v0 = du_'43''43''8314'_1538
du_'43''43''8314'_1538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_'43''43''8314'_1538 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      v4 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.++⁻
d_'43''43''8315'_1540 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''43''8315'_1540 ~v0 = du_'43''43''8315'_1540
du_'43''43''8315'_1540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'43''43''8315'_1540 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
      v4 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.+-assoc
d_'43''45'assoc_1542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_1542 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.+-comm
d_'43''45'comm_1544 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_1544 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.+-identityʳ
d_'43''45'identity'691'_1546 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691'_1546 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.+-suc
d_'43''45'suc_1548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'suc_1548 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.<-irrefl
d_'60''45'irrefl_1550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_1550 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.<-trans
d_'60''45'trans_1552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans_1552 ~v0 = du_'60''45'trans_1552
du_'60''45'trans_1552 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'trans_1552 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122 v1 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.<-≤-trans
d_'60''45''8804''45'trans_1554 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45''8804''45'trans_1554 ~v0
  = du_'60''45''8804''45'trans_1554
du_'60''45''8804''45'trans_1554 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45''8804''45'trans_1554 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractInstr
d_AbstractInstr_1556 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractTrace
d_AbstractTrace_1558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_AbstractTrace_1558 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.All
d_All_1560 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AllocMode
d_AllocMode_1562 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AllocState
d_AllocState_1564 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Carrier
d_Carrier_1574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_Carrier_1574 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Decimal
d_Decimal_1578 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.EffectShape
d_EffectShape_1582 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FitsInReg
d_FitsInReg_1586 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FitsInRegI
d_FitsInRegI_1588 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics
d_FrameSemantics_1590 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.HeapLocation
d_HeapLocation_1600 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.HeapRef
d_HeapRef_1604 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.IR
d_IR_1610 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.IRTy
d_IRTy_1612 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.LabelId
d_LabelId_1620 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.List
d_List_1624 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.LocState
d_LocState_1626 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Maybe
d_Maybe_1630 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.NatTr
d_NatTr_1632 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SigOpEvent
d_SigOpEvent_1652 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SigOpInfo
d_SigOpInfo_1656 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.StoredValue
d_StoredValue_1662 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Type
d_Type_1664 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValueLocation
d_ValueLocation_1670 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.WellFormedFI
d_WellFormedFI_1672 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.WellFormedFI-irrelevant
d_WellFormedFI'45'irrelevant_1674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedFI'45'irrelevant_1674 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.block-layout
d_block'45'layout_1682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_block'45'layout_1682 ~v0 = du_block'45'layout_1682
du_block'45'layout_1682 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_block'45'layout_1682
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'layout_2308
-- Once.CCC.Codegen.IRObsCorrect.Machine._.case_of_
d_case_of__1686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_case_of__1686 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_case_of__1686 v5 v6
du_case_of__1686 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_case_of__1686 v0 v1 = coe v1 v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.cong
d_cong_1688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_1688 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.cong₂
d_cong'8322'_1690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_cong'8322'_1690 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.current-frame
d_current'45'frame_1694 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 -> AgdaAny
d_current'45'frame_1694 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.effect
d_effect_1698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120
d_effect_1698 ~v0 = du_effect_1698
du_effect_1698 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120
du_effect_1698 v0 v1 v2
  = coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.exec-abstract-preserves-next-slot
d_exec'45'abstract'45'preserves'45'next'45'slot_1700 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'next'45'slot_1700 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.fits-in-reg?
d_fits'45'in'45'reg'63'_1708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192
d_fits'45'in'45'reg'63'_1708 ~v0 = du_fits'45'in'45'reg'63'_1708
du_fits'45'in'45'reg'63'_1708 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192
du_fits'45'in'45'reg'63'_1708
  = coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_200
-- Once.CCC.Codegen.IRObsCorrect.Machine._.halted
d_halted_1718 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_halted_1718 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.heap-ref
d_heap'45'ref_1722 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
d_heap'45'ref_1722 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.inject
d_inject_1730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_inject_1730 ~v0 = du_inject_1730
du_inject_1730 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_inject_1730
  = coe MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_458
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ir-size
d_ir'45'size_1750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'size_1750 ~v0 = du_ir'45'size_1750
du_ir'45'size_1750 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'size_1750 = coe MAlonzo.Code.Once.IR.Size.d_ir'45'size_10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.length
d_length_1754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer
d_length_1754 ~v0 = du_length_1754
du_length_1754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer
du_length_1754 v0 v1
  = coe MAlonzo.Code.Data.List.Base.du_length_268
-- Once.CCC.Codegen.IRObsCorrect.Machine._.length-++
d_length'45''43''43'_1756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''43''43'_1756 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.map
d_map_1764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_map_1764 ~v0 = du_map_1764
du_map_1764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_map_1764 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Data.List.Base.du_map_22 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.map
d_map_1768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_map_1768 ~v0 = du_map_1768
du_map_1768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_map_1768 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Data.Maybe.Base.du_map_64 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.m≤m+n
d_m'8804'm'43'n_1774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'm'43'n_1774 ~v0 = du_m'8804'm'43'n_1774
du_m'8804'm'43'n_1774 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'm'43'n_1774 v0 v1
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.m≤n+m
d_m'8804'n'43'm_1776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43'm_1776 ~v0 = du_m'8804'n'43'm_1776
du_m'8804'n'43'm_1776 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'43'm_1776 v0 v1
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636 v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.n<1+n
d_n'60'1'43'n_1778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'1'43'n_1778 ~v0 = du_n'60'1'43'n_1778
du_n'60'1'43'n_1778 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'60'1'43'n_1778
  = coe MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
-- Once.CCC.Codegen.IRObsCorrect.Machine._.next-heap-ref
d_next'45'heap'45'ref_1780 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 -> Integer
d_next'45'heap'45'ref_1780 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.next-slot
d_next'45'slot_1782 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 -> Integer
d_next'45'slot_1782 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.n≤1+n
d_n'8804'1'43'n_1786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'1'43'n_1786 ~v0 = du_n'8804'1'43'n_1786
du_n'8804'1'43'n_1786 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'8804'1'43'n_1786
  = coe MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
-- Once.CCC.Codegen.IRObsCorrect.Machine._.projTrace
d_projTrace_1790 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_projTrace_1790 ~v0 = du_projTrace_1790
du_projTrace_1790 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_projTrace_1790 v0 v1 v2
  = coe MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_64 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.fst
d_fst_1792 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_1792 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.snd
d_snd_1794 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_1794 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.readReg
d_readReg_1796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readReg_1796 ~v0 = du_readReg_1796
du_readReg_1796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readReg_1796 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ref-id
d_ref'45'id_1798 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 -> Integer
d_ref'45'id_1798 v0
  = coe MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.regs
d_regs_1802 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs_1802 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.round
d_round_1806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_round_1806 ~v0 = du_round_1806
du_round_1806 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
du_round_1806 = coe MAlonzo.Code.Once.Float.Decimal.d_round_174
-- Once.CCC.Codegen.IRObsCorrect.Machine._.subst
d_subst_1816 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_subst_1816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_subst_1816 v8
du_subst_1816 :: AgdaAny -> AgdaAny
du_subst_1816 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.subst₂
d_subst'8322'_1818 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_subst'8322'_1818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 v13
  = du_subst'8322'_1818 v13
du_subst'8322'_1818 :: AgdaAny -> AgdaAny
du_subst'8322'_1818 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.sucHL
d_sucHL_1822 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_sucHL_1822 ~v0 = du_sucHL_1822
du_sucHL_1822 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_sucHL_1822 = coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92
-- Once.CCC.Codegen.IRObsCorrect.Machine._.sucLoc
d_sucLoc_1824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sucLoc_1824 ~v0 = du_sucLoc_1824
du_sucLoc_1824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sucLoc_1824 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.sv-as-loc
d_sv'45'as'45'loc_1826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1826 ~v0 = du_sv'45'as'45'loc_1826
du_sv'45'as'45'loc_1826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1826 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1360 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.sym
d_sym_1828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1828 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.take
d_take_1830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> [AgdaAny] -> [AgdaAny]
d_take_1830 ~v0 = du_take_1830
du_take_1830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> [AgdaAny] -> [AgdaAny]
du_take_1830 v0 v1 v2 v3
  = coe MAlonzo.Code.Data.List.Base.du_take_530 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.trans
d_trans_1834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1834 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.writeReg
d_writeReg_1840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_writeReg_1840 ~v0 = du_writeReg_1840
du_writeReg_1840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_writeReg_1840 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.writeReg-preserves
d_writeReg'45'preserves_1842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_1842 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.writeReg-same
d_writeReg'45'same_1844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_1844 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ℓ
d_ℓ_1852 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_ℓ_1852 ~v0 = du_ℓ_1852
du_ℓ_1852 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_ℓ_1852 = coe MAlonzo.Code.Once.CCC.Label.d_ℓ_266
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Nat
d_Nat_1854 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Int
d_Int_1856 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.∃
d_'8707'_1858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> ()
d_'8707'_1858 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.∃-syntax
d_'8707''45'syntax_1860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> ()
d_'8707''45'syntax_1860 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.≤-<-trans
d_'8804''45''60''45'trans_1862 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45''60''45'trans_1862 ~v0
  = du_'8804''45''60''45'trans_1862
du_'8804''45''60''45'trans_1862 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45''60''45'trans_1862 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.≤-refl
d_'8804''45'refl_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'refl_1864 ~v0 = du_'8804''45'refl_1864
du_'8804''45'refl_1864 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'refl_1864
  = coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
-- Once.CCC.Codegen.IRObsCorrect.Machine._.≤-reflexive
d_'8804''45'reflexive_1866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'reflexive_1866 ~v0 = du_'8804''45'reflexive_1866
du_'8804''45'reflexive_1866 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'reflexive_1866 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896 v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.≤-trans
d_'8804''45'trans_1868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'trans_1868 ~v0 = du_'8804''45'trans_1868
du_'8804''45'trans_1868 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'trans_1868 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⊥
d_'8869'_1870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_'8869'_1870 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⊥-elim
d_'8869''45'elim_1872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim_1872 ~v0 = du_'8869''45'elim_1872
du_'8869''45'elim_1872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
du_'8869''45'elim_1872 v0 v1 v2
  = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⌊_⌋
d_'8970'_'8971'_1874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_'8970'_'8971'_1874 ~v0 = du_'8970'_'8971'_1874
du_'8970'_'8971'_1874 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
du_'8970'_'8971'_1874
  = coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⟦_,_⟧-baseI
d_'10214'_'44'_'10215''45'baseI_1876 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  () -> () -> MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'44'_'10215''45'baseI_1876 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_1878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_1878 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.⟦_⟧TI
d_'10214'_'10215'TI_1880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_'10214'_'10215'TI_1880 ~v0 = du_'10214'_'10215'TI_1880
du_'10214'_'10215'TI_1880 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
du_'10214'_'10215'TI_1880
  = coe MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.AllI
d_AllI_1896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_AllI_1896 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.BodyRunner
d_BodyRunner_1898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_1898 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.case-tag-at
d_case'45'tag'45'at_1900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_case'45'tag'45'at_1900 ~v0 = du_case'45'tag'45'at_1900
du_case'45'tag'45'at_1900 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_case'45'tag'45'at_1900 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_2860 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.combine-typed
d_combine'45'typed_1902 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_1902 ~v0 = du_combine'45'typed_1902
du_combine'45'typed_1902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_1902 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_combine'45'typed_2664 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-abstract
d_exec'45'abstract_1904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_1904 ~v0 = du_exec'45'abstract_1904
du_exec'45'abstract_1904 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_1904
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2954
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_1906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_1906 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_1908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_1908 ~v0
  = du_exec'45'case'45'dispatch_1908
du_exec'45'case'45'dispatch_1908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'case'45'dispatch_1908
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_2960
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_1910 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_1910 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_1912 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_1912 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_1914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_1914 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_1914
du_exec'45'load'45'from'45'slot'45'with'45'value_1914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_1914 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2606
      v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-loop
d_exec'45'loop_1916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_1916 ~v0 = du_exec'45'loop_1916
du_exec'45'loop_1916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop_1916
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'loop_2958
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-loop-run
d_exec'45'loop'45'run_1918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_1918 ~v0 = du_exec'45'loop'45'run_1918
du_exec'45'loop'45'run_1918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_1918 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_2888 v1
      v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_1920 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_1920 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_1922 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_1922 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_1924 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_1924 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_1924
du_exec'45'restore'45'input'45'with'45'value_1924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_1924 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2618
      v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_1926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_1926 ~v0 = du_exec'45'sigop'45'halts_1926
du_exec'45'sigop'45'halts_1926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts_1926 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_2854
      v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_1928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_1928 ~v0
  = du_exec'45'sigop'45'halts'45'of_1928
du_exec'45'sigop'45'halts'45'of_1928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts'45'of_1928 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_2848
      v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_1930 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_1930 ~v0
  = du_exec'45'sigop'45'output_1930
du_exec'45'sigop'45'output_1930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output_1930
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_2838
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_1932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_1932 ~v0
  = du_exec'45'sigop'45'output'45'of_1932
du_exec'45'sigop'45'output'45'of_1932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_1932
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2828
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-trace
d_exec'45'trace_1934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_1934 ~v0 = du_exec'45'trace_1934
du_exec'45'trace_1934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace_1934
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2956
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_1936 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_1936 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_1938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_1938 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_1940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_1940 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_1942 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_1942 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_1944 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2398 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_1944 ~v0
  = du_exec'45'tree'45'flat'45'equiv'45'simple_1944
du_exec'45'tree'45'flat'45'equiv'45'simple_1944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2398 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_1944 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'tree'45'flat'45'equiv'45'simple_3986
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_1946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2398 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_1946 ~v0 = du_exec'45'tree'45'trace_1946
du_exec'45'tree'45'trace_1946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2398 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'tree'45'trace_1946
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'tree'45'trace_3596
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_1948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2398 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_1948 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_1950 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_1950 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_1952 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_1952 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_1954 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2398 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2398 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_1954 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_1956 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_1956 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.getTag
d_getTag_1958 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> Maybe Integer
d_getTag_1958 ~v0 = du_getTag_1958
du_getTag_1958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> Maybe Integer
du_getTag_1958 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_getTag_3572 v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.lit-value
d_lit'45'value_1960 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 -> AgdaAny -> AgdaAny
d_lit'45'value_1960 ~v0 = du_lit'45'value_1960
du_lit'45'value_1960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 -> AgdaAny -> AgdaAny
du_lit'45'value_1960 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_lit'45'value_2948 v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_1962 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_loop'45'reanchor'45'alloc_1962 ~v0
  = du_loop'45'reanchor'45'alloc_1962
du_loop'45'reanchor'45'alloc_1962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_loop'45'reanchor'45'alloc_1962 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_2882
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.loop-reanchor-loc
d_loop'45'reanchor'45'loc_1964 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_loop'45'reanchor'45'loc_1964 ~v0
  = du_loop'45'reanchor'45'loc_1964
du_loop'45'reanchor'45'loc_1964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_loop'45'reanchor'45'loc_1964 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_2876
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_1966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_1966 ~v0
  = du_pure'45'sigop'45'out'45'aux_1966
du_pure'45'sigop'45'out'45'aux_1966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'aux_1966
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2792
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_1968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_1968 ~v0
  = du_pure'45'sigop'45'out'45'val_1968
du_pure'45'sigop'45'out'45'val_1968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_1968 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2776
      v0 v2 v3 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_1970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_1970 ~v0
  = du_pure'45'sigop'45'output_1970
du_pure'45'sigop'45'output_1970 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'output_1970
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_2770
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.readReg-typed
d_readReg'45'typed_1972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_1972 ~v0 = du_readReg'45'typed_1972
du_readReg'45'typed_1972 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_1972 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2728 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.readTyped
d_readTyped_1974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_readTyped_1974 ~v0 = du_readTyped_1974
du_readTyped_1974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_readTyped_1974 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2734 v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.readTyped-cell
d_readTyped'45'cell_1976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readTyped'45'cell_1976 ~v0 = du_readTyped'45'cell_1976
du_readTyped'45'cell_1976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readTyped'45'cell_1976 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'cell_2676 v2
      v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.readTyped-int
d_readTyped'45'int_1978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_readTyped'45'int_1978 ~v0 = du_readTyped'45'int_1978
du_readTyped'45'int_1978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_readTyped'45'int_1978 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'int_2670 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.readTyped-pair
d_readTyped'45'pair_1980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_readTyped'45'pair_1980 ~v0 = du_readTyped'45'pair_1980
du_readTyped'45'pair_1980 ::
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
du_readTyped'45'pair_1980 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'pair_2712 v3
      v4 v5 v6 v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_1982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_structured'45'pure'45'sigop'45'output_1982 ~v0
  = du_structured'45'pure'45'sigop'45'output_1982
du_structured'45'pure'45'sigop'45'output_1982 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_structured'45'pure'45'sigop'45'output_1982
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2764
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_1984 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_unit'45'storedvalue_1984 ~v0 = du_unit'45'storedvalue_1984
du_unit'45'storedvalue_1984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_unit'45'storedvalue_1984 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_unit'45'storedvalue_2658
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AllocState.block-size
d_block'45'size_2064 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> Integer
d_block'45'size_2064 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AllocState.current-frame
d_current'45'frame_2066 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 -> AgdaAny
d_current'45'frame_2066 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AllocState.frame-slots
d_frame'45'slots_2068 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 -> Integer
d_frame'45'slots_2068 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AllocState.next-heap-ref
d_next'45'heap'45'ref_2070 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 -> Integer
d_next'45'heap'45'ref_2070 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AllocState.next-slot
d_next'45'slot_2072 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 -> Integer
d_next'45'slot_2072 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.AllocState.saved-frames
d_saved'45'frames_2074 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_2074 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.AllSlotStable
d_AllSlotStable_2078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_AllSlotStable_2078 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.SlotStable
d_SlotStable_2080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_SlotStable_2080 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.SlotStableT
d_SlotStableT_2082 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_SlotStableT_2082 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.abstract-keeps-next-slot
d_abstract'45'keeps'45'next'45'slot_2084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abstract'45'keeps'45'next'45'slot_2084 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.case-keeps-next-slot
d_case'45'keeps'45'next'45'slot_2086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'keeps'45'next'45'slot_2086 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.elfs-alloc
d_elfs'45'alloc_2088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elfs'45'alloc_2088 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.eris-alloc
d_eris'45'alloc_2090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eris'45'alloc_2090 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.exec-flat-keeps-next-slot
d_exec'45'flat'45'keeps'45'next'45'slot_2092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'keeps'45'next'45'slot_2092 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.flat-keeps-next-slot
d_flat'45'keeps'45'next'45'slot_2094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'keeps'45'next'45'slot_2094 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.CataNextSlot.trace-keeps-next-slot
d_trace'45'keeps'45'next'45'slot_2096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'keeps'45'next'45'slot_2096 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Decimal.exp10
d_exp10_2100 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_exp10_2100 v0
  = coe MAlonzo.Code.Once.Float.Decimal.d_exp10_14 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.Decimal.sig
d_sig_2102 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_sig_2102 v0
  = coe MAlonzo.Code.Once.Float.Decimal.d_sig_12 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events
d_chain'45'events_2126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_chain'45'events_2126 ~v0 = du_chain'45'events_2126
du_chain'45'events_2126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_chain'45'events_2126 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_578 v0 v1
      v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-++
d_chain'45'events'45''43''43'_2128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_2128 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-len0
d_chain'45'events'45'len0_2130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'len0_2130 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-nil
d_chain'45'events'45'nil_2132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_2132 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-subst
d_chain'45'events'45'subst_2134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst_2134 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-subst-len
d_chain'45'events'45'subst'45'len_2136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'len_2136 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.chain-events-subst-start
d_chain'45'events'45'subst'45'start_2138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_2138 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.decode-arg
d_decode'45'arg_2140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_decode'45'arg_2140 ~v0 = du_decode'45'arg_2140
du_decode'45'arg_2140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_decode'45'arg_2140
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.d_decode'45'arg_388
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.decode-unread
d_decode'45'unread_2142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_decode'45'unread_2142 ~v0 = du_decode'45'unread_2142
du_decode'45'unread_2142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_decode'45'unread_2142
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.d_decode'45'unread_384
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.ev-of-loc
d_ev'45'of'45'loc_2144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_ev'45'of'45'loc_2144 ~v0 = du_ev'45'of'45'loc_2144
du_ev'45'of'45'loc_2144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_ev'45'of'45'loc_2144
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.d_ev'45'of'45'loc_410
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.event-of
d_event'45'of_2146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_event'45'of_2146 ~v0 = du_event'45'of_2146
du_event'45'of_2146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_event'45'of_2146
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.d_event'45'of_432
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events
d_flat'45'events_2148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'events_2148 ~v0 = du_flat'45'events_2148
du_flat'45'events_2148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_flat'45'events_2148
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_438
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-[]
d_flat'45'events'45''91''93'_2150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_2150 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-fetch
d_flat'45'events'45'fetch_2152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'events'45'fetch_2152 ~v0
  = du_flat'45'events'45'fetch_2152
du_flat'45'events'45'fetch_2152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_flat'45'events'45'fetch_2152
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'fetch_442
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-halted
d_flat'45'events'45'halted_2154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'halted_2154 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-reify
d_flat'45'events'45'reify_2156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_822 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'reify_2156 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-settled
d_flat'45'events'45'settled_2158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'settled_2158 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-step
d_flat'45'events'45'step_2160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'events'45'step_2160 ~v0 = du_flat'45'events'45'step_2160
du_flat'45'events'45'step_2160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_flat'45'events'45'step_2160
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'step_440
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.flat-events-steps
d_flat'45'events'45'steps_2162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'steps_2162 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatEventTrace.machine-event
d_machine'45'event_2164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118
d_machine'45'event_2164 ~v0 = du_machine'45'event_2164
du_machine'45'event_2164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118
du_machine'45'event_2164 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_machine'45'event_402 v0 v1
      v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.CallPost
d_CallPost_2168 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.FlatState
d_FlatState_2170 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.FlinkView
d_FlinkView_2174 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.ProgFree
d_ProgFree_2176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_ProgFree_2176 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.Shifted
d_Shifted_2178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Shifted_2178 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.Straight
d_Straight_2180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_Straight_2180 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.StraightStep
d_StraightStep_2182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_StraightStep_2182 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.callView
d_callView_2184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178
d_callView_2184 ~v0 = du_callView_2184
du_callView_2184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178
du_callView_2184
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1196
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-branch
d_do'45'branch_2190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_2190 ~v0 = du_do'45'branch_2190
du_do'45'branch_2190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch_2190
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_766
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-branch-at
d_do'45'branch'45'at_2192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch'45'at_2192 ~v0 = du_do'45'branch'45'at_2192
du_do'45'branch'45'at_2192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch'45'at_2192 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'branch'45'at_758 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-call
d_do'45'call_2194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_2194 ~v0 = du_do'45'call_2194
du_do'45'call_2194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call_2194
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1168
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-call-at
d_do'45'call'45'at_2196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_2196 ~v0 = du_do'45'call'45'at_2196
du_do'45'call'45'at_2196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'at_2196
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1112
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-call-code
d_do'45'call'45'code_2198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'code_2198 ~v0 = du_do'45'call'45'code_2198
du_do'45'call'45'code_2198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'code_2198
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'code_1120
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-call-code-prefix
d_do'45'call'45'code'45'prefix_2200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'code'45'prefix_2200 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-call-prefix
d_do'45'call'45'prefix_2202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'prefix_2202 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-call-sv
d_do'45'call'45'sv_2204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'sv_2204 ~v0 = du_do'45'call'45'sv_2204
du_do'45'call'45'sv_2204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'sv_2204
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'sv_1144
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-call-sv-prefix
d_do'45'call'45'sv'45'prefix_2206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'sv'45'prefix_2206 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-jump
d_do'45'jump_2208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_2208 ~v0 = du_do'45'jump_2208
du_do'45'jump_2208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_2208 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_750 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-ret
d_do'45'ret_2210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_2210 ~v0 = du_do'45'ret_2210
du_do'45'ret_2210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_2210 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_968 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-ret-alloc
d_do'45'ret'45'alloc_2212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_2212 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_2214 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_2214 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_2216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_2216 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_2218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_2218 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_2220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_2220 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-save-closure
d_do'45'save'45'closure_2222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'save'45'closure_2222 ~v0 = du_do'45'save'45'closure_2222
du_do'45'save'45'closure_2222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'save'45'closure_2222 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1326 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.do-thunk
d_do'45'thunk_2224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_2224 ~v0 = du_do'45'thunk_2224
du_do'45'thunk_2224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_2224
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1102
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.enter-call
d_enter'45'call_2226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_enter'45'call_2226 ~v0 = du_enter'45'call_2226
du_enter'45'call_2226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_enter'45'call_2226
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_788
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.enter-frame
d_enter'45'frame_2228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_enter'45'frame_2228 ~v0 = du_enter'45'frame_2228
du_enter'45'frame_2228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_enter'45'frame_2228
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'frame_782
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.exec-flat
d_exec'45'flat_2230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_2230 ~v0 = du_exec'45'flat_2230
du_exec'45'flat_2230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_exec'45'flat_2230
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3372
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.exec-flat-halted
d_exec'45'flat'45'halted_2232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_2232 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.exec-flat-invariant
d_exec'45'flat'45'invariant_2234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_2234 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.exec-flat-offend
d_exec'45'flat'45'offend_2236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_2236 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.exec-flat-reloc
d_exec'45'flat'45'reloc_2238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'flat'45'reloc_2238 ~v0 = du_exec'45'flat'45'reloc_2238
du_exec'45'flat'45'reloc_2238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'flat'45'reloc_2238 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'flat'45'reloc_3422 v0
      v1 v2 v3 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.exec-flat-step
d_exec'45'flat'45'step_2240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_2240 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_2242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_2242 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.exec-trace-halted
d_exec'45'trace'45'halted_2244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_2244 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_2246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_2246 ~v0
  = du_exec'45'trace'45'is'45'flat_2246
du_exec'45'trace'45'is'45'flat_2246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_2246 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'trace'45'is'45'flat_4198
      v1 v2 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.falloc
d_falloc_2248 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_2248 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fclosure
d_fclosure_2250 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_2250 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fetch
d_fetch_2252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
d_fetch_2252 ~v0 = du_fetch_2252
du_fetch_2252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
du_fetch_2252 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_214 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fetch-++-left
d_fetch'45''43''43''45'left_2254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'left_2254 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fetch-++-right
d_fetch'45''43''43''45'right_2256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'right_2256 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fetch-All
d_fetch'45'All_2258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_2258 ~v0 = du_fetch'45'All_2258
du_fetch'45'All_2258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_fetch'45'All_2258 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_3874 v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fetch-Straight
d_fetch'45'Straight_2260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_2260 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fetch-dispatch
d_fetch'45'dispatch_2262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fetch'45'dispatch_2262 ~v0 = du_fetch'45'dispatch_2262
du_fetch'45'dispatch_2262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fetch'45'dispatch_2262
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fetch'45'dispatch_3376
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.find-label
d_find'45'label_2264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_2264 ~v0 = du_find'45'label_2264
du_find'45'label_2264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_2264
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.find-label-lands
d_find'45'label'45'lands_2266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_2266 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.find-label-sound
d_find'45'label'45'sound_2268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_2268 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.find-thunk
d_find'45'thunk_2270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_2270 ~v0 = du_find'45'thunk_2270
du_find'45'thunk_2270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_2270
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_208
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.find-thunk-sound
d_find'45'thunk'45'sound_2272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_2272 ~v0 = du_find'45'thunk'45'sound_2272
du_find'45'thunk'45'sound_2272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'sound_2272 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'thunk'45'sound_724 v0
      v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fl-at
d_fl'45'at_2274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_2274 ~v0 = du_fl'45'at_2274
du_fl'45'at_2274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'at_2274
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'at_128
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fl-at-++-miss
d_fl'45'at'45''43''43''45'miss_2276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'at'45''43''43''45'miss_2276 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fl-go
d_fl'45'go_2278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_2278 ~v0 = du_fl'45'go_2278
du_fl'45'go_2278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'go_2278
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fl-go-++-miss
d_fl'45'go'45''43''43''45'miss_2280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45''43''43''45'miss_2280 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fl-go-lands
d_fl'45'go'45'lands_2282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_2282 ~v0 = du_fl'45'go'45'lands_2282
du_fl'45'go'45'lands_2282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_2282 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'lands_3658 v0 v1
      v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fl-go-sound
d_fl'45'go'45'sound_2284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_2284 ~v0 = du_fl'45'go'45'sound_2284
du_fl'45'go'45'sound_2284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_2284 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'sound_604 v0 v1
      v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fl-label-match
d_fl'45'label'45'match_2286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_2286 ~v0 = du_fl'45'label'45'match_2286
du_fl'45'label'45'match_2286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'label'45'match_2286
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fl-match-++-miss
d_fl'45'match'45''43''43''45'miss_2288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'match'45''43''43''45'miss_2288 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flat-exec-instr
d_flat'45'exec'45'instr_2290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_2290 ~v0 = du_flat'45'exec'45'instr_2290
du_flat'45'exec'45'instr_2290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_2290
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flat-exec-instr-prefix
d_flat'45'exec'45'instr'45'prefix_2292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prefix_2292 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flat-exec-instr-prog-irrelevant
d_flat'45'exec'45'instr'45'prog'45'irrelevant_2294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prog'45'irrelevant_2294 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flat-halt
d_flat'45'halt_2296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'halt_2296 ~v0 = du_flat'45'halt_2296
du_flat'45'halt_2296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'halt_2296 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'halt_1108 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flat-read-at
d_flat'45'read'45'at_2298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'at_2298 ~v0 = du_flat'45'read'45'at_2298
du_flat'45'read'45'at_2298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'at_2298 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'at_110 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flat-read-tag
d_flat'45'read'45'tag_2300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_2300 ~v0 = du_flat'45'read'45'tag_2300
du_flat'45'read'45'tag_2300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_2300 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flat-step-frame
d_flat'45'step'45'frame_2302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'frame_2302 ~v0 = du_flat'45'step'45'frame_2302
du_flat'45'step'45'frame_2302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'frame_2302
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'frame_960
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flat-step-straight
d_flat'45'step'45'straight_2304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'straight_2304 ~v0
  = du_flat'45'step'45'straight_2304
du_flat'45'step'45'straight_2304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'straight_2304
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flink
d_flink_2306 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_2306 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flink-do-branch
d_flink'45'do'45'branch_2308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch_2308 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flink-do-jump
d_flink'45'do'45'jump_2310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'jump_2310 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flink-do-ret
d_flink'45'do'45'ret_2312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'ret_2312 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.flinkView
d_flinkView_2314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3202
d_flinkView_2314 ~v0 = du_flinkView_2314
du_flinkView_2314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3202
du_flinkView_2314 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flinkView_3222 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.floc
d_floc_2316 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_2316 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.forced
d_forced_2318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_forced_2318 ~v0 = du_forced_2318
du_forced_2318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_forced_2318 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_4188 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fpc
d_fpc_2320 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_2320 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.fret
d_fret_2322 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_2322 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.ft-at
d_ft'45'at_2324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'at_2324 ~v0 = du_ft'45'at_2324
du_ft'45'at_2324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'at_2324
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'at_174
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.ft-at-++-miss
d_ft'45'at'45''43''43''45'miss_2326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45''43''43''45'miss_2326 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.ft-go
d_ft'45'go_2328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'go_2328 ~v0 = du_ft'45'go_2328
du_ft'45'go_2328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'go_2328
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_172
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.ft-go-++-miss
d_ft'45'go'45''43''43''45'miss_2330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45''43''43''45'miss_2330 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.ft-go-sound
d_ft'45'go'45'sound_2332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_2332 ~v0 = du_ft'45'go'45'sound_2332
du_ft'45'go'45'sound_2332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_2332 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_ft'45'go'45'sound_496 v0 v1
      v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.ft-match
d_ft'45'match_2334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'match_2334 ~v0 = du_ft'45'match_2334
du_ft'45'match_2334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'match_2334
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_176
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.ft-match-++-miss
d_ft'45'match'45''43''43''45'miss_2336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45''43''43''45'miss_2336 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.grow-frame
d_grow'45'frame_2344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_grow'45'frame_2344 ~v0 = du_grow'45'frame_2344
du_grow'45'frame_2344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_grow'45'frame_2344
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_grow'45'frame_1096
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.just-injℕ
d_just'45'injℕ_2346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_2346 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.lab-eq
d_lab'45'eq_2348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_2348 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.label-of?
d_label'45'of'63'_2350 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_2350 ~v0 = du_label'45'of'63'_2350
du_label'45'of'63'_2350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_2350 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_122 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.label-of?-sound
d_label'45'of'63''45'sound_2352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_2352 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.leave-frame
d_leave'45'frame_2354 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame_2354 ~v0 = du_leave'45'frame_2354
du_leave'45'frame_2354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame_2354 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_804 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.leave-frame-aux
d_leave'45'frame'45'aux_2356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame'45'aux_2356 ~v0 = du_leave'45'frame'45'aux_2356
du_leave'45'frame'45'aux_2356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame'45'aux_2356 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_792 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.leave-frame-block-size
d_leave'45'frame'45'block'45'size_2358 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_2358 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_2360 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_2360 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_2362 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_2362 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_2364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_2364 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_2366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_2366 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_2368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_2368 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_2370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_2370 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.mkFlat
d_mkFlat_2372 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_mkFlat_2372 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v0)
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.reloc-fetch
d_reloc'45'fetch_2376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'fetch_2376 ~v0 = du_reloc'45'fetch_2376
du_reloc'45'fetch_2376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'fetch_2376 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'fetch_3466 v0 v1 v2
      v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.reloc-step
d_reloc'45'step_2378 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'step_2378 ~v0 = du_reloc'45'step_2378
du_reloc'45'step_2378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'step_2378 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'step_3444 v0 v1 v2
      v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shift
d_shift_2380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_shift_2380 ~v0 = du_shift_2380
du_shift_2380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_shift_2380 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shift_3128 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shift-loc
d_shift'45'loc_2382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_2382 ~v0 = du_shift'45'loc_2382
du_shift'45'loc_2382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_2382 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shift'45'loc_4040 v0 v1 v3 v4
      v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-branch
d_shifted'45'branch_2384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'branch_2384 ~v0 = du_shifted'45'branch_2384
du_shifted'45'branch_2384 ::
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
du_shifted'45'branch_2384 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'branch_1642 v2 v5
      v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-call-at
d_shifted'45'call'45'at_2386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'at_2386 ~v0 = du_shifted'45'call'45'at_2386
du_shifted'45'call'45'at_2386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'at_2386 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'at_1780 v3
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-call-closure
d_shifted'45'call'45'closure_2388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'closure_2388 ~v0
  = du_shifted'45'call'45'closure_2388
du_shifted'45'call'45'closure_2388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'closure_2388 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'closure_1996
      v0 v3 v4 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-call-code
d_shifted'45'call'45'code_2390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'code_2390 ~v0
  = du_shifted'45'call'45'code_2390
du_shifted'45'call'45'code_2390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'code_2390 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'code_1828
      v0 v2 v4 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-call-sv
d_shifted'45'call'45'sv_2392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'sv_2392 ~v0 = du_shifted'45'call'45'sv_2392
du_shifted'45'call'45'sv_2392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'sv_2392 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'sv_1910 v0
      v2 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-eq
d_shifted'45'eq_2394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shifted'45'eq_2394 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-frame
d_shifted'45'frame_2396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'frame_2396 ~v0 = du_shifted'45'frame_2396
du_shifted'45'frame_2396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'frame_2396 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'frame_1680 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-halt
d_shifted'45'halt_2398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'halt_2398 ~v0 = du_shifted'45'halt_2398
du_shifted'45'halt_2398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'halt_2398 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'halt_1746 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-instr
d_shifted'45'instr_2400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'instr_2400 ~v0 = du_shifted'45'instr_2400
du_shifted'45'instr_2400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'instr_2400 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'instr_2036 v0 v2
      v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-jump
d_shifted'45'jump_2402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'jump_2402 ~v0 = du_shifted'45'jump_2402
du_shifted'45'jump_2402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'jump_2402 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'jump_1584 v3 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-label
d_shifted'45'label_2404 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'label_2404 ~v0 = du_shifted'45'label_2404
du_shifted'45'label_2404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'label_2404 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'label_1442 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-ret
d_shifted'45'ret_2406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret_2406 ~v0 = du_shifted'45'ret_2406
du_shifted'45'ret_2406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret_2406 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret_1560 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-ret-aux
d_shifted'45'ret'45'aux_2408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret'45'aux_2408 ~v0 = du_shifted'45'ret'45'aux_2408
du_shifted'45'ret'45'aux_2408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret'45'aux_2408 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret'45'aux_1508 v3
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-save-closure
d_shifted'45'save'45'closure_2410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'save'45'closure_2410 ~v0
  = du_shifted'45'save'45'closure_2410
du_shifted'45'save'45'closure_2410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'save'45'closure_2410 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'save'45'closure_1718
      v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-shift
d_shifted'45'shift_2412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'shift_2412 ~v0 = du_shifted'45'shift_2412
du_shifted'45'shift_2412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'shift_2412 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'shift_3142
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-straight
d_shifted'45'straight_2414 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'straight_2414 ~v0 = du_shifted'45'straight_2414
du_shifted'45'straight_2414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'straight_2414 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'straight_1406 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.shifted-thunk
d_shifted'45'thunk_2416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'thunk_2416 ~v0 = du_shifted'45'thunk_2416
du_shifted'45'thunk_2416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'thunk_2416 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'thunk_1470 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.step-dispatch
d_step'45'dispatch_2418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_step'45'dispatch_2418 ~v0 = du_step'45'dispatch_2418
du_step'45'dispatch_2418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_step'45'dispatch_2418
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_step'45'dispatch_3374
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.sv-is-zero
d_sv'45'is'45'zero_2420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_2420 ~v0 = du_sv'45'is'45'zero_2420
du_sv'45'is'45'zero_2420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_2420 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.tag-zf
d_tag'45'zf_2422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_2422 ~v0 = du_tag'45'zf_2422
du_tag'45'zf_2422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_2422 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.thunk-of?
d_thunk'45'of'63'_2424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_2424 ~v0 = du_thunk'45'of'63'_2424
du_thunk'45'of'63'_2424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_2424 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63'_168 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.thunk-of?-sound
d_thunk'45'of'63''45'sound_2426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_2426 ~v0
  = du_thunk'45'of'63''45'sound_2426
du_thunk'45'of'63''45'sound_2426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_2426 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63''45'sound_476
      v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.≡ᵇ-true
d_'8801''7495''45'true_2428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_2428 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.FlatState.falloc
d_falloc_2438 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_2438 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.FlatState.fclosure
d_fclosure_2440 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_2440 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.FlatState.flink
d_flink_2442 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_2442 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.FlatState.floc
d_floc_2444 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_2444 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.FlatState.fpc
d_fpc_2446 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_2446 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatMachine.FlatState.fret
d_fret_2448 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_2448 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.FlatSteps
d_FlatSteps_2462 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.FlatSteps-++
d_FlatSteps'45''43''43'_2464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45''43''43'_2464 ~v0 = du_FlatSteps'45''43''43'_2464
du_FlatSteps'45''43''43'_2464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45''43''43'_2464 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1138
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.FlatSteps-middle
d_FlatSteps'45'middle_2466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45'middle_2466 ~v0 = du_FlatSteps'45'middle_2466
du_FlatSteps'45'middle_2466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45'middle_2466 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'middle_1058
      v9
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.FlatSteps-prefix
d_FlatSteps'45'prefix_2468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45'prefix_2468 ~v0 = du_FlatSteps'45'prefix_2468
du_FlatSteps'45'prefix_2468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45'prefix_2468 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'prefix_966
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.FlatSteps-reloc
d_FlatSteps'45'reloc_2470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45'reloc_2470 ~v0 = du_FlatSteps'45'reloc_2470
du_FlatSteps'45'reloc_2470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45'reloc_2470 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'reloc_1008
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.RunReified
d_RunReified_2472 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.chain-steps
d_chain'45'steps_2478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_chain'45'steps_2478 ~v0 = du_chain'45'steps_2478
du_chain'45'steps_2478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_chain'45'steps_2478 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_chain'45'steps_1158
      v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.chain-steps-nil
d_chain'45'steps'45'nil_2480 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  (Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68) ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'steps'45'nil_2480 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.exec-flat-steps
d_exec'45'flat'45'steps_2482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_2482 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.fetch-++
d_fetch'45''43''43'_2484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43'_2484 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.find-label-distrib
d_find'45'label'45'distrib_2486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'distrib_2486 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.fl-go-prefix
d_fl'45'go'45'prefix_2488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'prefix_2488 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.fl-go-shift
d_fl'45'go'45'shift_2490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'shift_2490 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.fl-go-skip
d_fl'45'go'45'skip_2492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45'skip_2492 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.flat-jmp
d_flat'45'jmp_2494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'jmp_2494 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.flat-label
d_flat'45'label_2496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'label_2496 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.flat-scratch-branch-not
d_flat'45'scratch'45'branch'45'not_2498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'not_2498 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.flat-scratch-branch-yes
d_flat'45'scratch'45'branch'45'yes_2500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'scratch'45'branch'45'yes_2500 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.flat-step1
d_flat'45'step1_2502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_flat'45'step1_2502 ~v0 = du_flat'45'step1_2502
du_flat'45'step1_2502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_flat'45'step1_2502 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_flat'45'step1_382
      v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.flat-tag-branch-not
d_flat'45'tag'45'branch'45'not_2504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'not_2504 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.flat-tag-branch-yes
d_flat'45'tag'45'branch'45'yes_2506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'tag'45'branch'45'yes_2506 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.flm-prefix
d_flm'45'prefix_2508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'prefix_2508 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.flm-shift
d_flm'45'shift_2510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flm'45'shift_2510 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.link-block-steps
d_link'45'block'45'steps_2512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2292 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_link'45'block'45'steps_2512 ~v0 = du_link'45'block'45'steps_2512
du_link'45'block'45'steps_2512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2292 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_link'45'block'45'steps_2512 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_link'45'block'45'steps_1102
      v13
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.reify-run
d_reify'45'run_2516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_822
d_reify'45'run_2516 ~v0 = du_reify'45'run_2516
du_reify'45'run_2516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_822
du_reify'45'run_2516
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_reify'45'run_862
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.RunReified.chain
d_chain_2526 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_822 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_chain_2526 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_chain_848 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.RunReified.fuel-split
d_fuel'45'split_2528 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_822 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_2528 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.RunReified.rest-fuel
d_rest'45'fuel_2530 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_822 ->
  Integer
d_rest'45'fuel_2530 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_rest'45'fuel_844
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.RunReified.settle
d_settle_2532 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_822 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_2532 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settle_846 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.RunReified.settled
d_settled_2534 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_822 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_2534 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settled_850 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FlatStepsAPI.RunReified.steps-len
d_steps'45'len_2536 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_822 ->
  Integer
d_steps'45'len_2536 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_steps'45'len_842
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics._≟F_
d__'8799'F__2540 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__2540 v0
  = coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics._≺_
d__'8826'__2542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> ()
d__'8826'__2542 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.Frame
d_Frame_2544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_Frame_2544 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.float-format
d_float'45'format_2546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_2546 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_124 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.frame-base
d_frame'45'base_2548 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
d_frame'45'base_2548 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_2550 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.frame-word
d_frame'45'word_2552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_frame'45'word_2552 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_108 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_2554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_2554 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word'45'pos_110
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.shift-base
d_shift'45'base_2556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_2556 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.shift-frame
d_shift'45'frame_2558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_2558 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_106 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.slot-addr
d_slot'45'addr_2560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_2560 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_2562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_2562 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.slot-injective
d_slot'45'injective_2564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_2564 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_2566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_2566 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.≺-compare
d_'8826''45'compare_2568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_2568 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'compare_144
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_2570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_2570 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrameSemantics.≺-trans
d_'8826''45'trans_2572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_2572 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_134 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.AllocBump
d_AllocBump_2576 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.BeforeFrontier
d_BeforeFrontier_2580 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.StackAncestorSource
d_StackAncestorSource_2582 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.apply-bump
d_apply'45'bump_2584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_apply'45'bump_2584 ~v0 = du_apply'45'bump_2584
du_apply'45'bump_2584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_apply'45'bump_2584 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_936 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_2586 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_2586 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.apply-bump-compose
d_apply'45'bump'45'compose_2588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_2588 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_2590 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_2590 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_2592 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_2592 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.bump-+
d_bump'45''43'_2594 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924
d_bump'45''43'_2594 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_mkBump_934
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_930
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_930
            (coe v1)))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_932
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_932
            (coe v1)))
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.bump-0
d_bump'45'0_2596 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924
d_bump'45'0_2596 ~v0 = du_bump'45'0_2596
du_bump'45'0_2596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924
du_bump'45'0_2596 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Allocation.du_bump'45'0_942
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.fresh-stack-after
d_fresh'45'stack'45'after_2598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_2598 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.frontier-monotone
d_frontier'45'monotone_2600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_frontier'45'monotone_2600 ~v0 = du_frontier'45'monotone_2600
du_frontier'45'monotone_2600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_frontier'45'monotone_2600 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.heap-alloc-advances
d_heap'45'alloc'45'advances_2602 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_heap'45'alloc'45'advances_2602 ~v0
  = du_heap'45'alloc'45'advances_2602
du_heap'45'alloc'45'advances_2602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_heap'45'alloc'45'advances_2602 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_heap'45'alloc'45'advances_828
      v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_2608 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 -> Integer
d_next'45'heap'45'ref'45'delta_2608 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_932
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.next-slot-delta
d_next'45'slot'45'delta_2610 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 -> Integer
d_next'45'slot'45'delta_2610 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_930
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.stack-alloc-advances
d_stack'45'alloc'45'advances_2616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_stack'45'alloc'45'advances_2616 ~v0
  = du_stack'45'alloc'45'advances_2616
du_stack'45'alloc'45'advances_2616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_stack'45'alloc'45'advances_2616 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      v1 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.≺⇒≢
d_'8826''8658''8802'_2622 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_2622 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_2626 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 -> Integer
d_next'45'heap'45'ref'45'delta_2626 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_932
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.FrontierInvariant.AllocBump.next-slot-delta
d_next'45'slot'45'delta_2628 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 -> Integer
d_next'45'slot'45'delta_2628 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_930
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.HeapLocation.heap-offset
d_heap'45'offset_2646 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_heap'45'offset_2646 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.HeapLocation.heap-ref
d_heap'45'ref_2648 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
d_heap'45'ref_2648 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.HeapRef.ref-id
d_ref'45'id_2652 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 -> Integer
d_ref'45'id_2652 v0
  = coe MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.LocState-eq
d_LocState'45'eq_2730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_LocState'45'eq_2730 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.REFUTABLE-effect-state-only-frame-dep
d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2732 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  AgdaAny
d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2732 ~v0
  = du_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2732
du_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  AgdaAny
du_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2732
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2848
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.case-on-tag-state-next-slot-invariant
d_case'45'on'45'tag'45'state'45'next'45'slot'45'invariant_2734 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'on'45'tag'45'state'45'next'45'slot'45'invariant_2734
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.exec-abstract-deterministic
d_exec'45'abstract'45'deterministic_2736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'deterministic_2736 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_2738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_2738 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_2740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_2740 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_2742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_2742 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.exec-abstract-same-frame
d_exec'45'abstract'45'same'45'frame_2744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'same'45'frame_2744 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.exec-abstract-state-next-slot-invariant
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_2746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_2746
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.exec-case-dispatch-preserves-frame
d_exec'45'case'45'dispatch'45'preserves'45'frame_2748 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'case'45'dispatch'45'preserves'45'frame_2748 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.exec-loop-preserves-frame
d_exec'45'loop'45'preserves'45'frame_2750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'loop'45'preserves'45'frame_2750 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.exec-trace-preserves-frame
d_exec'45'trace'45'preserves'45'frame_2752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'frame_2752 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.loop-state-next-slot-invariant
d_loop'45'state'45'next'45'slot'45'invariant_2754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loop'45'state'45'next'45'slot'45'invariant_2754 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.next-slot-update-preserves-frame
d_next'45'slot'45'update'45'preserves'45'frame_2756 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'frame_2756 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.next-slot-update-preserves-heap-ref
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_2758 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_2758 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.store-at-slot-preserves-above
d_store'45'at'45'slot'45'preserves'45'above_2760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'above_2760 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_2762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_2762 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_2764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_2764 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.InstrPrimitives.worklist-push-preserves-stack-slot
d_worklist'45'push'45'preserves'45'stack'45'slot_2766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_worklist'45'push'45'preserves'45'stack'45'slot_2766 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.LabelId.idx
d_idx_2770 :: MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_idx_2770 v0 = coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.LabelId.owner
d_owner_2772 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_owner_2772 v0
  = coe MAlonzo.Code.Once.CCC.Label.d_owner_14 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.LabelId.path
d_path_2774 :: MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> [Integer]
d_path_2774 v0 = coe MAlonzo.Code.Once.CCC.Label.d_path_16 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.LocState.halted
d_halted_2784 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_halted_2784 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.LocState.heapMem
d_heapMem_2786 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_heapMem_2786 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.LocState.regs
d_regs_2788 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs_2788 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.LocState.stackMem
d_stackMem_2790 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_stackMem_2790 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.clear-frame
d_clear'45'frame_2800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_clear'45'frame_2800 ~v0 = du_clear'45'frame_2800
du_clear'45'frame_2800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_clear'45'frame_2800
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_clear'45'frame_700
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.clear-frame-aux
d_clear'45'frame'45'aux_2802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_clear'45'frame'45'aux_2802 ~v0 = du_clear'45'frame'45'aux_2802
du_clear'45'frame'45'aux_2802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_clear'45'frame'45'aux_2802 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_clear'45'frame'45'aux_694
      v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.clear-frame-just
d_clear'45'frame'45'just_2804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_clear'45'frame'45'just_2804 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.readHeapLoc
d_readHeapLoc_2806 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readHeapLoc_2806 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418 v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.readLoc
d_readLoc_2808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_2808 ~v0 = du_readLoc_2808
du_readLoc_2808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_2808 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.readStackLoc
d_readStackLoc_2810 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readStackLoc_2810 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 v0 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeHeapMem
d_writeHeapMem_2812 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem_2812 ~v0 = du_writeHeapMem_2812
du_writeHeapMem_2812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem_2812 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_782 v1 v2 v3
      v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_2814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem'45'aux_2814 ~v0 = du_writeHeapMem'45'aux_2814
du_writeHeapMem'45'aux_2814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem'45'aux_2814 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_776 v3
      v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLoc
d_writeLoc_2816 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_2816 ~v0 = du_writeLoc_2816
du_writeLoc_2816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLoc_2816
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_810
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLoc-halted
d_writeLoc'45'halted_2818 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2818 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2820 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2820 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2822 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2822 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2824 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2826 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLoc-regs
d_writeLoc'45'regs_2828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2828 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2830 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2830 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLocToHeap
d_writeLocToHeap_2832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToHeap_2832 ~v0 = du_writeLocToHeap_2832
du_writeLocToHeap_2832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToHeap_2832 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_802 v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeLocToStack
d_writeLocToStack_2834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToStack_2834 ~v0 = du_writeLocToStack_2834
du_writeLocToStack_2834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToStack_2834
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_792
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeStackMem
d_writeStackMem_2836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_writeStackMem_2836 ~v0 = du_writeStackMem_2836
du_writeStackMem_2836 ::
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
du_writeStackMem_2836
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeStackMem_672
-- Once.CCC.Codegen.IRObsCorrect.Machine._.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_2838 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_writeStackMem'45'aux_2838 ~v0 = du_writeStackMem'45'aux_2838
du_writeStackMem'45'aux_2838 ::
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
du_writeStackMem'45'aux_2838 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_664 v5
      v6 v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ReadLocEq.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_2860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_2860 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.REFUTABLE-alloc-heap-trace-preserves-heap-ref
d_REFUTABLE'45'alloc'45'heap'45'trace'45'preserves'45'heap'45'ref_2864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_REFUTABLE'45'alloc'45'heap'45'trace'45'preserves'45'heap'45'ref_2864
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.case-on-tag-trace-preserves-heap-ref
d_case'45'on'45'tag'45'trace'45'preserves'45'heap'45'ref_2866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'on'45'tag'45'trace'45'preserves'45'heap'45'ref_2866
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-instr-load-tag-lit-preserves-alloc
d_exec'45'abstract'45'instr'45'load'45'tag'45'lit'45'preserves'45'alloc_2868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'instr'45'load'45'tag'45'lit'45'preserves'45'alloc_2868
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-from-slot-output
d_exec'45'abstract'45'load'45'from'45'slot'45'output_2870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'from'45'slot'45'output_2870 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-from-slot-preserves-alloc
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'alloc_2872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'alloc_2872
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-from-slot-preserves-mem
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'mem_2874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'mem_2874
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-output
d_exec'45'abstract'45'load'45'indirect'45'output_2876 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'output_2876 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-alloc
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'alloc_2878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'alloc_2878
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-heapMem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'heapMem_2880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'heapMem_2880
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-input
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'input_2882 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'input_2882
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_2884 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_2884
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-preserves-stackMem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'stackMem_2886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'stackMem_2886
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-suc-output
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_2888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_2888
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-alloc
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'alloc_2890 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'alloc_2890
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-heapMem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'heapMem_2892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'heapMem_2892
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-input
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'input_2894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'input_2894
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_2896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_2896
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-stackMem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'stackMem_2898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'stackMem_2898
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-mov-to-input-input
d_exec'45'abstract'45'mov'45'to'45'input'45'input_2900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'input_2900 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-alloc
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'alloc_2902 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'alloc_2902
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-heapMem
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'heapMem_2904 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'heapMem_2904
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-mem
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'mem_2906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'mem_2906
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-stackMem
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'stackMem_2908 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'stackMem_2908
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-mov-to-output-preserves-alloc
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'alloc_2910 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'alloc_2910
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-mov-to-output-preserves-mem
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'mem_2912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'mem_2912
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-preserves-heap-ref
d_exec'45'abstract'45'preserves'45'heap'45'ref_2914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heap'45'ref_2914 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-restore-input-preserves-alloc
d_exec'45'abstract'45'restore'45'input'45'preserves'45'alloc_2916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'preserves'45'alloc_2916
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-restore-input-preserves-heapMem
d_exec'45'abstract'45'restore'45'input'45'preserves'45'heapMem_2918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'preserves'45'heapMem_2918
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-restore-input-preserves-stackMem
d_exec'45'abstract'45'restore'45'input'45'preserves'45'stackMem_2920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'preserves'45'stackMem_2920
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-restore-input-sets-input
d_exec'45'abstract'45'restore'45'input'45'sets'45'input_2922 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'sets'45'input_2922
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-store-at-slot-preserves-alloc
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'alloc_2924 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'alloc_2924
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-store-indirect-preserves-alloc
d_exec'45'abstract'45'store'45'indirect'45'preserves'45'alloc_2926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'indirect'45'preserves'45'alloc_2926
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-abstract-store-indirect-suc-preserves-alloc
d_exec'45'abstract'45'store'45'indirect'45'suc'45'preserves'45'alloc_2928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'indirect'45'suc'45'preserves'45'alloc_2928
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.exec-trace-preserves-heap-ref
d_exec'45'trace'45'preserves'45'heap'45'ref_2930 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heap'45'ref_2930 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.load-indirect-halted-success
d_load'45'indirect'45'halted'45'success_2932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'indirect'45'halted'45'success_2932 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.load-indirect-suc-halted-success
d_load'45'indirect'45'suc'45'halted'45'success_2934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'indirect'45'suc'45'halted'45'success_2934 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.loop-trace-preserves-heap-ref
d_loop'45'trace'45'preserves'45'heap'45'ref_2936 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loop'45'trace'45'preserves'45'heap'45'ref_2936 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.passthrough-mem-preserved
d_passthrough'45'mem'45'preserved_2938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_passthrough'45'mem'45'preserved_2938 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.passthrough-output-is-input
d_passthrough'45'output'45'is'45'input_2940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_passthrough'45'output'45'is'45'input_2940 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.passthrough-preserves-halted
d_passthrough'45'preserves'45'halted_2942 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_passthrough'45'preserves'45'halted_2942 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-left-setup-alloc-helper
d_prod'45'left'45'setup'45'alloc'45'helper_2944 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'alloc'45'helper_2944 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-left-setup-halted-helper
d_prod'45'left'45'setup'45'halted'45'helper_2946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'halted'45'helper_2946 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-left-setup-input-helper
d_prod'45'left'45'setup'45'input'45'helper_2948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'input'45'helper_2948 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-left-setup-mem-helper
d_prod'45'left'45'setup'45'mem'45'helper_2950 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'mem'45'helper_2950 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-left-setup-saves-input
d_prod'45'left'45'setup'45'saves'45'input_2952 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'saves'45'input_2952 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-right-setup-alloc-helper
d_prod'45'right'45'setup'45'alloc'45'helper_2954 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'alloc'45'helper_2954 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-right-setup-halted-helper
d_prod'45'right'45'setup'45'halted'45'helper_2956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'halted'45'helper_2956 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-right-setup-input-helper
d_prod'45'right'45'setup'45'input'45'helper_2958 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'input'45'helper_2958 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-right-setup-mem-helper
d_prod'45'right'45'setup'45'mem'45'helper_2960 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'mem'45'helper_2960 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-setup-trace-exec
d_prod'45'setup'45'trace'45'exec_2962 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'exec_2962 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-setup-trace-preserves-alloc
d_prod'45'setup'45'trace'45'preserves'45'alloc_2964 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'alloc_2964 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-setup-trace-preserves-halted
d_prod'45'setup'45'trace'45'preserves'45'halted_2966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'halted_2966 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-setup-trace-preserves-heapMem
d_prod'45'setup'45'trace'45'preserves'45'heapMem_2968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'heapMem_2968 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-setup-trace-preserves-stackMem
d_prod'45'setup'45'trace'45'preserves'45'stackMem_2970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'stackMem_2970 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.prod-setup-trace-sets-input
d_prod'45'setup'45'trace'45'sets'45'input_2972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'sets'45'input_2972 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-alloc-correct-4
d_rec'45'scheme'45'alloc'45'correct'45'4_2974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'alloc'45'correct'45'4_2974 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-output-is-input
d_rec'45'scheme'45'output'45'is'45'input_2976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'output'45'is'45'input_2976 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-output-is-slot
d_rec'45'scheme'45'output'45'is'45'slot_2978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'output'45'is'45'slot_2978 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-output-is-slot-4
d_rec'45'scheme'45'output'45'is'45'slot'45'4_2980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'output'45'is'45'slot'45'4_2980 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-preserves-ancestor-3
d_rec'45'scheme'45'preserves'45'ancestor'45'3_2982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'ancestor'45'3_2982 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-preserves-ancestor-4
d_rec'45'scheme'45'preserves'45'ancestor'45'4_2984 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'ancestor'45'4_2984 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-preserves-halted
d_rec'45'scheme'45'preserves'45'halted_2986 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'halted_2986 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-preserves-halted-3
d_rec'45'scheme'45'preserves'45'halted'45'3_2988 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'halted'45'3_2988 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-preserves-halted-4
d_rec'45'scheme'45'preserves'45'halted'45'4_2990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'halted'45'4_2990 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-preserves-heap-3
d_rec'45'scheme'45'preserves'45'heap'45'3_2992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'heap'45'3_2992 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-preserves-heap-4
d_rec'45'scheme'45'preserves'45'heap'45'4_2994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'heap'45'4_2994 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-preserves-slot-below-3
d_rec'45'scheme'45'preserves'45'slot'45'below'45'3_2996 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'slot'45'below'45'3_2996 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-preserves-slot-below-4
d_rec'45'scheme'45'preserves'45'slot'45'below'45'4_2998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'slot'45'below'45'4_2998 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-stores-input
d_rec'45'scheme'45'stores'45'input_3000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'stores'45'input_3000 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-stores-input-3
d_rec'45'scheme'45'stores'45'input'45'3_3002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'stores'45'input'45'3_3002 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.rec-scheme-trace-4
d_rec'45'scheme'45'trace'45'4_3004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_rec'45'scheme'45'trace'45'4_3004 ~v0
  = du_rec'45'scheme'45'trace'45'4_3004
du_rec'45'scheme'45'trace'45'4_3004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_rec'45'scheme'45'trace'45'4_3004 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_rec'45'scheme'45'trace'45'4_11174
      v1
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.restore-trace-preserves-alloc
d_restore'45'trace'45'preserves'45'alloc_3006 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'trace'45'preserves'45'alloc_3006 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.restore-trace-preserves-heapMem
d_restore'45'trace'45'preserves'45'heapMem_3008 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'trace'45'preserves'45'heapMem_3008 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.restore-trace-preserves-stackMem
d_restore'45'trace'45'preserves'45'stackMem_3010 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'trace'45'preserves'45'stackMem_3010 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.setup-trace-exec
d_setup'45'trace'45'exec_3012 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'exec_3012 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.setup-trace-preserves-alloc
d_setup'45'trace'45'preserves'45'alloc_3014 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'alloc_3014 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.setup-trace-preserves-halted
d_setup'45'trace'45'preserves'45'halted_3016 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'halted_3016 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.setup-trace-preserves-heapMem
d_setup'45'trace'45'preserves'45'heapMem_3018 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'heapMem_3018 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.setup-trace-preserves-stackMem
d_setup'45'trace'45'preserves'45'stackMem_3020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'stackMem_3020 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.RecSchemeSemantics.setup-trace-sets-input
d_setup'45'trace'45'sets'45'input_3022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'sets'45'input_3022 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SigOpEvent.ev-arg
d_ev'45'arg_3026 ::
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118 -> AgdaAny
d_ev'45'arg_3026 v0
  = coe MAlonzo.Code.Once.Denotation.Trace.d_ev'45'arg_134 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SigOpEvent.ev-dom
d_ev'45'dom_3030 ::
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_ev'45'dom_3030 v0
  = coe MAlonzo.Code.Once.Denotation.Trace.d_ev'45'dom_130 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SigOpEvent.ev-name
d_ev'45'name_3032 ::
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_ev'45'name_3032 v0
  = coe MAlonzo.Code.Once.Denotation.Trace.d_ev'45'name_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SigOpInfo.baseA
d_baseA_3036 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_baseA_3036 v0
  = coe MAlonzo.Code.Once.SigOp.Info.d_baseA_178 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SigOpInfo.conB
d_conB_3038 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.SigOp.Info.T_Linkage_148
d_conB_3038 v0
  = coe MAlonzo.Code.Once.SigOp.Info.d_conB_180 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SigOpInfo.name
d_name_3040 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_name_3040 v0
  = coe MAlonzo.Code.Once.SigOp.Info.d_name_174 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.SigOpInfo.sem
d_sem_3042 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_134
d_sem_3042 v0 = coe MAlonzo.Code.Once.SigOp.Info.d_sem_176 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.InstrPreservesHalted
d_InstrPreservesHalted_3056 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.InstrWF
d_InstrWF_3058 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_InstrWF_3058 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.InstrWF-frame-eq
d_InstrWF'45'frame'45'eq_3060 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_InstrWF'45'frame'45'eq_3060 ~v0 = du_InstrWF'45'frame'45'eq_3060
du_InstrWF'45'frame'45'eq_3060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
du_InstrWF'45'frame'45'eq_3060 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_InstrWF'45'frame'45'eq_8894
      v1 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.TracePreservesHaltedP
d_TracePreservesHaltedP_3062 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.TraceWF
d_TraceWF_3064 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.TraceWF-alloc-eq
d_TraceWF'45'alloc'45'eq_3066 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294
d_TraceWF'45'alloc'45'eq_3066 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_TraceWF'45'alloc'45'eq_3066 v7
du_TraceWF'45'alloc'45'eq_3066 ::
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294
du_TraceWF'45'alloc'45'eq_3066 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.TraceWF-frame-eq
d_TraceWF'45'frame'45'eq_3068 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294
d_TraceWF'45'frame'45'eq_3068 ~v0 = du_TraceWF'45'frame'45'eq_3068
du_TraceWF'45'frame'45'eq_3068 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294
du_TraceWF'45'frame'45'eq_3068 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_TraceWF'45'frame'45'eq_9574
      v1 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.case-on-tag-preserves-halted
d_case'45'on'45'tag'45'preserves'45'halted_3070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'on'45'tag'45'preserves'45'halted_3070 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-abstract-preserves-halted
d_exec'45'abstract'45'preserves'45'halted_3072 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrPreservesHalted_7958 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted_3072 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-abstract-preserves-halted-WF
d_exec'45'abstract'45'preserves'45'halted'45'WF_3074 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted'45'WF_3074 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-abstract-state-frame-eq
d_exec'45'abstract'45'state'45'frame'45'eq_3076 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'frame'45'eq_3076 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-abstract-store-at-slot-preserves-input
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'input_3078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'input_3078
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-abstract-store-at-slot-preserves-loc
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'loc_3080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'loc_3080
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-deterministic
d_exec'45'trace'45'deterministic_3082 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'deterministic_3082 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-final-lea-mov-input
d_exec'45'trace'45'final'45'lea'45'mov'45'input_3084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'final'45'lea'45'mov'45'input_3084 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-final-lea-slot
d_exec'45'trace'45'final'45'lea'45'slot_3086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'final'45'lea'45'slot_3086 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-independent
d_exec'45'trace'45'independent_3088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'independent_3088 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-independent-below
d_exec'45'trace'45'independent'45'below_3090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
d_exec'45'trace'45'independent'45'below_3090 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-ancestor
d_exec'45'trace'45'preserves'45'ancestor_3092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'ancestor_3092 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-ancestor-nonwrite
d_exec'45'trace'45'preserves'45'ancestor'45'nonwrite_3094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'ancestor'45'nonwrite_3094 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-halted
d_exec'45'trace'45'preserves'45'halted_3096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'halted_3096 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-halted-WF
d_exec'45'trace'45'preserves'45'halted'45'WF_3098 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'halted'45'WF_3098 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-heap-loc
d_exec'45'trace'45'preserves'45'heap'45'loc_3100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heap'45'loc_3100 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-heapMem
d_exec'45'trace'45'preserves'45'heapMem_3102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heapMem_3102 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-slot-above
d_exec'45'trace'45'preserves'45'slot'45'above_3104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'above_3104 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-slot-above-nonwrite
d_exec'45'trace'45'preserves'45'slot'45'above'45'nonwrite_3106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'above'45'nonwrite_3106
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-slot-below
d_exec'45'trace'45'preserves'45'slot'45'below_3108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'below_3108 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-preserves-slot-below-nonwrite
d_exec'45'trace'45'preserves'45'slot'45'below'45'nonwrite_3110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'below'45'nonwrite_3110
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-same-frame
d_exec'45'trace'45'same'45'frame_3112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'same'45'frame_3112 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-slot-value
d_exec'45'trace'45'slot'45'value_3114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'slot'45'value_3114 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-slot-value-below
d_exec'45'trace'45'slot'45'value'45'below_3116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'slot'45'value'45'below_3116 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-snoc
d_exec'45'trace'45'snoc_3118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'snoc_3118 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-snoc-state
d_exec'45'trace'45'snoc'45'state_3120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'snoc'45'state_3120 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.exec-trace-state-frame-eq
d_exec'45'trace'45'state'45'frame'45'eq_3122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'state'45'frame'45'eq_3122 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.lea-slot-halted
d_lea'45'slot'45'halted_3156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'halted_3156 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.lea-slot-preserves-mem
d_lea'45'slot'45'preserves'45'mem_3158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'preserves'45'mem_3158 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.lea-slot-result
d_lea'45'slot'45'result_3160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'result_3160 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.load-indirect-suc-twf
d_load'45'indirect'45'suc'45'twf_3162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'twf_3162 ~v0
  = du_load'45'indirect'45'suc'45'twf_3162
du_load'45'indirect'45'suc'45'twf_3162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'twf_3162 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'suc'45'twf_8284
      v3 v4 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.load-indirect-twf
d_load'45'indirect'45'twf_3164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'twf_3164 ~v0
  = du_load'45'indirect'45'twf_3164
du_load'45'indirect'45'twf_3164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'twf_3164 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'twf_8266
      v3 v4 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.loop-preserves-halted
d_loop'45'preserves'45'halted_3166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loop'45'preserves'45'halted_3166 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.prefix-store-preserve
d_prefix'45'store'45'preserve_3168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prefix'45'store'45'preserve_3168 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.sigop-preserves-halted
d_sigop'45'preserves'45'halted_3170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'preserves'45'halted_3170 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.store-at-slot-halted
d_store'45'at'45'slot'45'halted_3172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'halted_3172 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.store-at-slot-preserves-other
d_store'45'at'45'slot'45'preserves'45'other_3174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'other_3174 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.store-at-slot-regs
d_store'45'at'45'slot'45'regs_3176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'regs_3176 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.store-at-slot-result
d_store'45'at'45'slot'45'result_3178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'result_3178 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.store-then-preserve
d_store'45'then'45'preserve_3180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'then'45'preserve_3180 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.tph-++
d_tph'45''43''43'_3182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8142 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8142 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8142
d_tph'45''43''43'_3182 ~v0 = du_tph'45''43''43'_3182
du_tph'45''43''43'_3182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8142 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8142 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TracePreservesHaltedP_8142
du_tph'45''43''43'_3182 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_tph'45''43''43'_8194
      v1 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.twf-++
d_twf'45''43''43'_3188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294
d_twf'45''43''43'_3188 ~v0 = du_twf'45''43''43'_3188
du_twf'45''43''43'_3188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294
du_twf'45''43''43'_3188 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_twf'45''43''43'_8806
      v1 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine._.TracePrimitives.twf-++-decomp
d_twf'45''43''43''45'decomp_3190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_twf'45''43''43''45'decomp_3190 ~v0
  = du_twf'45''43''43''45'decomp_3190
du_twf'45''43''43''45'decomp_3190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_twf'45''43''43''45'decomp_3190 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_twf'45''43''43''45'decomp_8848
      v1 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid
d_ClosureValid_3268 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InlValid
d_InlValid_3272 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InrValid
d_InrValid_3276 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid
d_PairValid_3280 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ValidAt
d_ValidAt_3284 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.composeClosure
d_composeClosure_3286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_composeClosure_3286 ~v0 = du_composeClosure_3286
du_composeClosure_3286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
du_composeClosure_3286 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16 v17 v18
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.du_composeClosure_758 v3 v6
      v7 v8 v10 v11 v15 v16 v17 v18
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.composeInl
d_composeInl_3288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_composeInl_3288 ~v0 = du_composeInl_3288
du_composeInl_3288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
du_composeInl_3288 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.du_composeInl_800 v7 v10 v11
      v12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.composeInr
d_composeInr_3290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_composeInr_3290 ~v0 = du_composeInr_3290
du_composeInr_3290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
du_composeInr_3290 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.du_composeInr_832 v7 v10 v11
      v12
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.composePair
d_composePair_3292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_composePair_3292 ~v0 = du_composePair_3292
du_composePair_3292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
du_composePair_3292 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.du_composePair_706 v8 v9 v13
      v14 v15 v16 v17
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.decomposeClosure
d_decomposeClosure_3294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374
d_decomposeClosure_3294 ~v0 = du_decomposeClosure_3294
du_decomposeClosure_3294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374
du_decomposeClosure_3294 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.du_decomposeClosure_602 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.decomposeInl
d_decomposeInl_3296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InlValid_458
d_decomposeInl_3296 ~v0 = du_decomposeInl_3296
du_decomposeInl_3296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InlValid_458
du_decomposeInl_3296 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.du_decomposeInl_640 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.decomposeInr
d_decomposeInr_3298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InrValid_514
d_decomposeInr_3298 ~v0 = du_decomposeInr_3298
du_decomposeInr_3298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InrValid_514
du_decomposeInr_3298 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.du_decomposeInr_670 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.decomposePair
d_decomposePair_3300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310
d_decomposePair_3300 ~v0 = du_decomposePair_3300
du_decomposePair_3300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310
du_decomposePair_3300 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.du_decomposePair_570 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.eval
d_eval_3302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_eval_3302 ~v0 = du_eval_3302
du_eval_3302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_eval_3302 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.CCC.Machine.Validity.du_eval_100 v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_3304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_3304 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.validity-mem-only
d_validity'45'mem'45'only_3316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_validity'45'mem'45'only_3316 ~v0
  = du_validity'45'mem'45'only_3316
du_validity'45'mem'45'only_3316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
du_validity'45'mem'45'only_3316 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.du_validity'45'mem'45'only_866
      v0 v1 v2 v3 v4 v6 v7 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.EnvType
d_EnvType_3320 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_3320 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Validity.d_EnvType_416 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.body
d_body_3322 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_body_3322 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Validity.d_body_418 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.body<bound
d_body'60'bound_3324 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_body'60'bound_3324 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_body'60'bound_422 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.code-before
d_code'45'before_3326 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_code'45'before_3326 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_code'45'before_434
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.code-loc
d_code'45'loc_3328 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_code'45'loc_3328 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_code'45'loc_426 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.code-ptr
d_code'45'ptr_3330 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_3330 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.env
d_env_3332 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  AgdaAny
d_env_3332 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Validity.d_env_420 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.env-before
d_env'45'before_3334 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_env'45'before_3334 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_env'45'before_432 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.env-loc
d_env'45'loc_3336 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_env'45'loc_3336 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_env'45'loc_424 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.env-ptr
d_env'45'ptr_3338 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_3338 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.env-valid
d_env'45'valid_3340 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_env'45'valid_3340 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_env'45'valid_438 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.f-is-closure
d_f'45'is'45'closure_3342 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_3342 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.ClosureValid.sucLoc-before
d_sucLoc'45'before_3344 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_3344 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_sucLoc'45'before_436
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InlValid.a
d_a_3348 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InlValid_458 -> AgdaAny
d_a_3348 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Validity.d_a_486 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InlValid.payload-before
d_payload'45'before_3350 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InlValid_458 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_payload'45'before_3350 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_payload'45'before_492
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InlValid.payload-loc
d_payload'45'loc_3352 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InlValid_458 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_3352 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_payload'45'loc_488
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InlValid.payload-ptr
d_payload'45'ptr_3354 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InlValid_458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_3354 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InlValid.payload-valid
d_payload'45'valid_3356 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InlValid_458 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_payload'45'valid_3356 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_payload'45'valid_496
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InlValid.sucLoc-before
d_sucLoc'45'before_3358 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InlValid_458 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_3358 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_sucLoc'45'before_494
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InlValid.v-is-inl
d_v'45'is'45'inl_3360 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InlValid_458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_3360 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InrValid.b
d_b_3364 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InrValid_514 -> AgdaAny
d_b_3364 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Validity.d_b_542 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InrValid.payload-before
d_payload'45'before_3366 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InrValid_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_payload'45'before_3366 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_payload'45'before_548
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InrValid.payload-loc
d_payload'45'loc_3368 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InrValid_514 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_3368 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_payload'45'loc_544
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InrValid.payload-ptr
d_payload'45'ptr_3370 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InrValid_514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_3370 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InrValid.payload-valid
d_payload'45'valid_3372 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InrValid_514 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_payload'45'valid_3372 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_payload'45'valid_552
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InrValid.sucLoc-before
d_sucLoc'45'before_3374 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InrValid_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_3374 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_sucLoc'45'before_550
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.InrValid.v-is-inr
d_v'45'is'45'inr_3376 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_InrValid_514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_3376 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid.fst-before
d_fst'45'before_3380 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_fst'45'before_3380 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_fst'45'before_350 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid.fst-loc
d_fst'45'loc_3382 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_fst'45'loc_3382 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_fst'45'loc_342 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid.fst-ptr
d_fst'45'ptr_3384 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'ptr_3384 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid.fst-valid
d_fst'45'valid_3386 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_fst'45'valid_3386 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_fst'45'valid_356 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid.snd-before
d_snd'45'before_3388 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_snd'45'before_3388 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_snd'45'before_352 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid.snd-loc
d_snd'45'loc_3390 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_snd'45'loc_3390 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_snd'45'loc_344 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid.snd-ptr
d_snd'45'ptr_3392 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'ptr_3392 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid.snd-valid
d_snd'45'valid_3394 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Validity.T_ValidAt_218
d_snd'45'valid_3394 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_snd'45'valid_358 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine._.ValidityDef.PairValid.sucLoc-before
d_sucLoc'45'before_3396 ::
  MAlonzo.Code.Once.CCC.Machine.Validity.T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_3396 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Validity.d_sucLoc'45'before_354
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.AllSlotStable
d_AllSlotStable_3446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_AllSlotStable_3446 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BeforeFrontier
d_BeforeFrontier_3448 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlockAt
d_BlockAt_3450 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockAt_3450 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlockRuns
d_BlockRuns_3452 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlocksAt
d_BlocksAt_3456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_BlocksAt_3456 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CallPost
d_CallPost_3458 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun
d_CalleeRun_3460 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRuns
d_CalleeRuns_3464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_CalleeRuns_3464 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CellAt
d_CellAt_3466 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CoalgRuns
d_CoalgRuns_3468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_CoalgRuns_3468 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.EnvAt
d_EnvAt_3470 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState
d_FlatState_3472 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatSteps
d_FlatSteps_3476 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatSteps-++
d_FlatSteps'45''43''43'_3478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45''43''43'_3478 ~v0 ~v1
  = du_FlatSteps'45''43''43'_3478
du_FlatSteps'45''43''43'_3478 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45''43''43'_3478 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1138
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatSteps-prefix
d_FlatSteps'45'prefix_3480 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45'prefix_3480 ~v0 ~v1 = du_FlatSteps'45'prefix_3480
du_FlatSteps'45'prefix_3480 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45'prefix_3480 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'prefix_966
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatSteps-reloc
d_FlatSteps'45'reloc_3482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_FlatSteps'45'reloc_3482 ~v0 ~v1 = du_FlatSteps'45'reloc_3482
du_FlatSteps'45'reloc_3482 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
du_FlatSteps'45'reloc_3482 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45'reloc_1008
      v6
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlinkView
d_FlinkView_3484 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.IRObsCorrectF
d_IRObsCorrectF_3486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_3486 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.InlineRep
d_InlineRep_3488 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.InputAt
d_InputAt_3490 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.InstrWF
d_InstrWF_3492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_InstrWF_3492 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.MachineRefinesObsF
d_MachineRefinesObsF_3494 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ProgFree
d_ProgFree_3498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_ProgFree_3498 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.Readable
d_Readable_3500 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ResultPlace
d_ResultPlace_3502 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.Shifted
d_Shifted_3504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Shifted_3504 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.SpanAt
d_SpanAt_3506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_SpanAt_3506 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.Straight
d_Straight_3508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_Straight_3508 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.StraightStep
d_StraightStep_3510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_StraightStep_3510 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValidAtWF
d_ValidAtWF_3512 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized
d_ValueRealized_3514 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.blocks
d_blocks_3524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_3524 v0 ~v1 = du_blocks_3524 v0
du_blocks_3524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_blocks_3524 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_blocks_3376
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.callView
d_callView_3526 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178
d_callView_3526 ~v0 v1 = du_callView_3526 v1
du_callView_3526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1178
du_callView_3526 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1196 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.cata-correct
d_cata'45'correct_3530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   Integer ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
   (Integer ->
    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
   Integer ->
   MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3706 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660
d_cata'45'correct_3530 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cata'45'correct_3974
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.chain-events
d_chain'45'events_3536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_chain'45'events_3536 ~v0 v1 = du_chain'45'events_3536 v1
du_chain'45'events_3536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_chain'45'events_3536 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_578
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.chain-events-++
d_chain'45'events'45''43''43'_3538 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_3538 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.chain-events-nil
d_chain'45'events'45'nil_3540 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_3540 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.chain-events-subst-start
d_chain'45'events'45'subst'45'start_3542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_3542 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.decomposeClosureWF
d_decomposeClosureWF_3548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668
d_decomposeClosureWF_3548 ~v0 ~v1 = du_decomposeClosureWF_3548
du_decomposeClosureWF_3548 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1668
du_decomposeClosureWF_3548 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1738
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.decomposePairWF
d_decomposePairWF_3550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892
d_decomposePairWF_3550 ~v0 ~v1 = du_decomposePairWF_3550
du_decomposePairWF_3550 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1892
du_decomposePairWF_3550 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1934
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-branch
d_do'45'branch_3552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_3552 ~v0 v1 = du_do'45'branch_3552 v1
du_do'45'branch_3552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch_3552 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_766 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-branch-at
d_do'45'branch'45'at_3554 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch'45'at_3554 ~v0 ~v1 = du_do'45'branch'45'at_3554
du_do'45'branch'45'at_3554 ::
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch'45'at_3554
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'branch'45'at_758
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call
d_do'45'call_3556 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_3556 ~v0 v1 = du_do'45'call_3556 v1
du_do'45'call_3556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call_3556 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1168 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-at
d_do'45'call'45'at_3558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_3558 ~v0 v1 = du_do'45'call'45'at_3558 v1
du_do'45'call'45'at_3558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'at_3558 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1112 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-code
d_do'45'call'45'code_3560 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'code_3560 ~v0 v1 = du_do'45'call'45'code_3560 v1
du_do'45'call'45'code_3560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'code_3560 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'code_1120
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-code-prefix
d_do'45'call'45'code'45'prefix_3562 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'code'45'prefix_3562 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-prefix
d_do'45'call'45'prefix_3564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'prefix_3564 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-sv
d_do'45'call'45'sv_3566 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'sv_3566 ~v0 v1 = du_do'45'call'45'sv_3566 v1
du_do'45'call'45'sv_3566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'sv_3566 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'sv_1144 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-call-sv-prefix
d_do'45'call'45'sv'45'prefix_3568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'sv'45'prefix_3568 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-jump
d_do'45'jump_3570 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_3570 ~v0 ~v1 = du_do'45'jump_3570
du_do'45'jump_3570 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_3570
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_750
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret
d_do'45'ret_3572 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_3572 ~v0 ~v1 = du_do'45'ret_3572
du_do'45'ret_3572 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_3572
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_968
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-alloc
d_do'45'ret'45'alloc_3574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_3574 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_3576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_3576 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_3578 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_3578 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_3580 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_3580 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_3582 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_3582 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-save-closure
d_do'45'save'45'closure_3584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'save'45'closure_3584 ~v0 ~v1
  = du_do'45'save'45'closure_3584
du_do'45'save'45'closure_3584 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'save'45'closure_3584
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1326
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.do-thunk
d_do'45'thunk_3586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_3586 ~v0 v1 = du_do'45'thunk_3586 v1
du_do'45'thunk_3586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_3586 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1102 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.emitted
d_emitted_3588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_emitted_3588 v0 ~v1 = du_emitted_3588 v0
du_emitted_3588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_emitted_3588 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_3364
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.enter-call
d_enter'45'call_3590 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_enter'45'call_3590 ~v0 v1 = du_enter'45'call_3590 v1
du_enter'45'call_3590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_enter'45'call_3590 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_788 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.enter-frame
d_enter'45'frame_3592 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_enter'45'frame_3592 ~v0 v1 = du_enter'45'frame_3592 v1
du_enter'45'frame_3592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_enter'45'frame_3592 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'frame_782 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.event-of
d_event'45'of_3604 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_event'45'of_3604 ~v0 v1 = du_event'45'of_3604 v1
du_event'45'of_3604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_event'45'of_3604 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_event'45'of_432 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract
d_exec'45'abstract_3606 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_3606 ~v0 v1 = du_exec'45'abstract_3606 v1
du_exec'45'abstract_3606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_3606 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2954
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-load-indirect-output
d_exec'45'abstract'45'load'45'indirect'45'output_3608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'output_3608 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-load-indirect-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_3610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_3610
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-load-indirect-suc-output
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_3612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_3612
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-load-indirect-suc-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_3614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_3614
  = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_3616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_3616 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-halted-WF
d_exec'45'abstract'45'preserves'45'halted'45'WF_3618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted'45'WF_3618 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-heap-ref
d_exec'45'abstract'45'preserves'45'heap'45'ref_3620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heap'45'ref_3620 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_3622 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_3622 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_3624 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_3624 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat
d_exec'45'flat_3626 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_exec'45'flat_3626 ~v0 v1 = du_exec'45'flat_3626 v1
du_exec'45'flat_3626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_exec'45'flat_3626 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_3372 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-halted
d_exec'45'flat'45'halted_3628 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_3628 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-invariant
d_exec'45'flat'45'invariant_3630 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_3630 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-keeps-next-slot
d_exec'45'flat'45'keeps'45'next'45'slot_3632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'keeps'45'next'45'slot_3632 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-offend
d_exec'45'flat'45'offend_3634 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_3634 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-reloc
d_exec'45'flat'45'reloc_3636 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'flat'45'reloc_3636 ~v0 v1
  = du_exec'45'flat'45'reloc_3636 v1
du_exec'45'flat'45'reloc_3636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'flat'45'reloc_3636 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'flat'45'reloc_3422
      (coe v0) v1 v2 v3 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-step
d_exec'45'flat'45'step_3638 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_3638 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-steps
d_exec'45'flat'45'steps_3640 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'steps_3640 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-stop
d_exec'45'flat'45'stop_3642 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'stop_3642 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_3644 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_3644 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-sigop-halts
d_exec'45'sigop'45'halts_3646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_3646 ~v0 ~v1
  = du_exec'45'sigop'45'halts_3646
du_exec'45'sigop'45'halts_3646 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts_3646 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_2854
      v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_3648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_3648 ~v0 ~v1
  = du_exec'45'sigop'45'halts'45'of_3648
du_exec'45'sigop'45'halts'45'of_3648 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts'45'of_3648 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_2848
      v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_3650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_3650 ~v0 v1
  = du_exec'45'sigop'45'output'45'of_3650 v1
du_exec'45'sigop'45'output'45'of_3650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_3650 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2828
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-trace-halted
d_exec'45'trace'45'halted_3652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_3652 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_3654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_3654 ~v0 ~v1
  = du_exec'45'trace'45'is'45'flat_3654
du_exec'45'trace'45'is'45'flat_3654 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_3654 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_exec'45'trace'45'is'45'flat_4198
      v0 v1 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch
d_fetch_3660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
d_fetch_3660 ~v0 ~v1 = du_fetch_3660
du_fetch_3660 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
du_fetch_3660 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_214
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-++-left
d_fetch'45''43''43''45'left_3662 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'left_3662 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-++-right
d_fetch'45''43''43''45'right_3664 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'right_3664 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-All
d_fetch'45'All_3666 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_3666 ~v0 ~v1 = du_fetch'45'All_3666
du_fetch'45'All_3666 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_fetch'45'All_3666 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_3874 v1 v2 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-Straight
d_fetch'45'Straight_3668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_3668 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fetch-dispatch
d_fetch'45'dispatch_3670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fetch'45'dispatch_3670 ~v0 v1 = du_fetch'45'dispatch_3670 v1
du_fetch'45'dispatch_3670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fetch'45'dispatch_3670 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fetch'45'dispatch_3376
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-label
d_find'45'label_3672 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_3672 ~v0 v1 = du_find'45'label_3672 v1
du_find'45'label_3672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_3672 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-label-lands
d_find'45'label'45'lands_3674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_3674 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-label-sound
d_find'45'label'45'sound_3676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_3676 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-thunk
d_find'45'thunk_3678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_3678 ~v0 v1 = du_find'45'thunk_3678 v1
du_find'45'thunk_3678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_3678 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_208 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.find-thunk-sound
d_find'45'thunk'45'sound_3680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_3680 ~v0 v1
  = du_find'45'thunk'45'sound_3680 v1
du_find'45'thunk'45'sound_3680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'sound_3680 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'thunk'45'sound_724
      (coe v0) v1 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-at
d_fl'45'at_3682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_3682 ~v0 v1 = du_fl'45'at_3682 v1
du_fl'45'at_3682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'at_3682 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'at_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-at-++-miss
d_fl'45'at'45''43''43''45'miss_3684 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'at'45''43''43''45'miss_3684 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-go
d_fl'45'go_3686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_3686 ~v0 v1 = du_fl'45'go_3686 v1
du_fl'45'go_3686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'go_3686 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-go-++-miss
d_fl'45'go'45''43''43''45'miss_3688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45''43''43''45'miss_3688 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-go-lands
d_fl'45'go'45'lands_3690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_3690 ~v0 v1 = du_fl'45'go'45'lands_3690 v1
du_fl'45'go'45'lands_3690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_3690 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'lands_3658
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-go-sound
d_fl'45'go'45'sound_3692 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_3692 ~v0 v1 = du_fl'45'go'45'sound_3692 v1
du_fl'45'go'45'sound_3692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_3692 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fl'45'go'45'sound_604
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-label-match
d_fl'45'label'45'match_3694 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_3694 ~v0 v1
  = du_fl'45'label'45'match_3694 v1
du_fl'45'label'45'match_3694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'label'45'match_3694 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.fl-match-++-miss
d_fl'45'match'45''43''43''45'miss_3696 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'match'45''43''43''45'miss_3696 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-events
d_flat'45'events_3698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'events_3698 ~v0 v1 = du_flat'45'events_3698 v1
du_flat'45'events_3698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_flat'45'events_3698 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_438 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-events-[]
d_flat'45'events'45''91''93'_3700 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_3700 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-exec-instr
d_flat'45'exec'45'instr_3702 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_3702 ~v0 v1
  = du_flat'45'exec'45'instr_3702 v1
du_flat'45'exec'45'instr_3702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_3702 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-exec-instr-prefix
d_flat'45'exec'45'instr'45'prefix_3704 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prefix_3704 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-exec-instr-prog-irrelevant
d_flat'45'exec'45'instr'45'prog'45'irrelevant_3706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prog'45'irrelevant_3706 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-halt
d_flat'45'halt_3708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'halt_3708 ~v0 ~v1 = du_flat'45'halt_3708
du_flat'45'halt_3708 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'halt_3708
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'halt_1108
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-read-at
d_flat'45'read'45'at_3710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'at_3710 ~v0 ~v1 = du_flat'45'read'45'at_3710
du_flat'45'read'45'at_3710 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'at_3710
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'at_110
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-read-tag
d_flat'45'read'45'tag_3712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_3712 ~v0 ~v1 = du_flat'45'read'45'tag_3712
du_flat'45'read'45'tag_3712 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_3712
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-step-frame
d_flat'45'step'45'frame_3718 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'frame_3718 ~v0 v1
  = du_flat'45'step'45'frame_3718 v1
du_flat'45'step'45'frame_3718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'frame_3718 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'frame_960
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flat-step-straight
d_flat'45'step'45'straight_3720 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'step'45'straight_3720 ~v0 v1
  = du_flat'45'step'45'straight_3720 v1
du_flat'45'step'45'straight_3720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'step'45'straight_3720 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flink-do-branch
d_flink'45'do'45'branch_3724 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch_3724 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flink-do-jump
d_flink'45'do'45'jump_3726 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'jump_3726 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flink-do-ret
d_flink'45'do'45'ret_3728 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'ret_3728 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.flinkView
d_flinkView_3730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3202
d_flinkView_3730 ~v0 ~v1 = du_flinkView_3730
du_flinkView_3730 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3202
du_flinkView_3730
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flinkView_3222
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.forced
d_forced_3734 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_forced_3734 ~v0 ~v1 = du_forced_3734
du_forced_3734 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_forced_3734
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_4188
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.frontier-monotone
d_frontier'45'monotone_3740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_frontier'45'monotone_3740 ~v0 ~v1 = du_frontier'45'monotone_3740
du_frontier'45'monotone_3740 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_frontier'45'monotone_3740 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-at
d_ft'45'at_3742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'at_3742 ~v0 v1 = du_ft'45'at_3742 v1
du_ft'45'at_3742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'at_3742 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'at_174 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-at-++-miss
d_ft'45'at'45''43''43''45'miss_3744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45''43''43''45'miss_3744 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-go
d_ft'45'go_3746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'go_3746 ~v0 v1 = du_ft'45'go_3746 v1
du_ft'45'go_3746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'go_3746 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_172 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-go-++-miss
d_ft'45'go'45''43''43''45'miss_3748 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45''43''43''45'miss_3748 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-go-sound
d_ft'45'go'45'sound_3750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_3750 ~v0 v1 = du_ft'45'go'45'sound_3750 v1
du_ft'45'go'45'sound_3750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_3750 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_ft'45'go'45'sound_496
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-match
d_ft'45'match_3752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'match_3752 ~v0 v1 = du_ft'45'match_3752 v1
du_ft'45'match_3752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'match_3752 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_176 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ft-match-++-miss
d_ft'45'match'45''43''43''45'miss_3754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45''43''43''45'miss_3754 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.grow-frame
d_grow'45'frame_3762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_grow'45'frame_3762 ~v0 v1 = du_grow'45'frame_3762 v1
du_grow'45'frame_3762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_grow'45'frame_3762 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_grow'45'frame_1096 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.inline-sv
d_inline'45'sv_3770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_3770 ~v0 ~v1 = du_inline'45'sv_3770
du_inline'45'sv_3770 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_3770 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_572
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ir-stable
d_ir'45'stable_3772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_3772 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'stable_520
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_3774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_3774 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_876
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.just-injℕ
d_just'45'injℕ_3776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_3776 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.lab-eq
d_lab'45'eq_3778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_3778 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.label-of?
d_label'45'of'63'_3780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_3780 ~v0 ~v1 = du_label'45'of'63'_3780
du_label'45'of'63'_3780 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_3780
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_label'45'of'63'_122
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.label-of?-sound
d_label'45'of'63''45'sound_3782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_3782 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame
d_leave'45'frame_3784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame_3784 ~v0 ~v1 = du_leave'45'frame_3784
du_leave'45'frame_3784 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame_3784
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_804
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-aux
d_leave'45'frame'45'aux_3786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame'45'aux_3786 ~v0 ~v1
  = du_leave'45'frame'45'aux_3786
du_leave'45'frame'45'aux_3786 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame'45'aux_3786
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_792
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-block-size
d_leave'45'frame'45'block'45'size_3788 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_3788 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_3790 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_3790 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_3792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_3792 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_3794 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_3794 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_3796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_3796 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_3798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_3798 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_3800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_3800 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.load-indirect-suc-twf
d_load'45'indirect'45'suc'45'twf_3802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'twf_3802 ~v0 ~v1
  = du_load'45'indirect'45'suc'45'twf_3802
du_load'45'indirect'45'suc'45'twf_3802 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'twf_3802 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'suc'45'twf_8284
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.load-indirect-twf
d_load'45'indirect'45'twf_3804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'twf_3804 ~v0 ~v1
  = du_load'45'indirect'45'twf_3804
du_load'45'indirect'45'twf_3804 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'twf_3804 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.du_load'45'indirect'45'twf_8266
      v2 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.prim-sv
d_prim'45'sv_3810 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_3810 ~v0 ~v1 = du_prim'45'sv_3810
du_prim'45'sv_3810 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_3810 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_554
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_3812 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_3812 ~v0 v1
  = du_pure'45'sigop'45'out'45'aux_3812 v1
du_pure'45'sigop'45'out'45'aux_3812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'aux_3812 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_2792
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_3814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_3814 ~v0 v1
  = du_pure'45'sigop'45'out'45'val_3814 v1
du_pure'45'sigop'45'out'45'val_3814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'out'45'val_3814 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_pure'45'sigop'45'out'45'val_2776
      (coe v0) v2 v3 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.pure-sigop-output
d_pure'45'sigop'45'output_3816 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_3816 ~v0 v1
  = du_pure'45'sigop'45'output_3816 v1
du_pure'45'sigop'45'output_3816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_pure'45'sigop'45'output_3816 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_2770
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readLoc
d_readLoc_3824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_3824 ~v0 ~v1 = du_readLoc_3824
du_readLoc_3824 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_3824
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_3826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_3826 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readReg-typed
d_readReg'45'typed_3828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_3828 ~v0 ~v1 = du_readReg'45'typed_3828
du_readReg'45'typed_3828 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_3828
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2728
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readTyped
d_readTyped_3830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_readTyped_3830 ~v0 ~v1 = du_readTyped_3830
du_readTyped_3830 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_readTyped_3830
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2734
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readTyped-adequate
d_readTyped'45'adequate_3832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_854 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'adequate_3832 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.readable?
d_readable'63'_3834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_854
d_readable'63'_3834 ~v0 ~v1 = du_readable'63'_3834
du_readable'63'_3834 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe
    MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_854
du_readable'63'_3834
  = coe
      MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'63'_868
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.reloc-fetch
d_reloc'45'fetch_3840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'fetch_3840 ~v0 v1 = du_reloc'45'fetch_3840 v1
du_reloc'45'fetch_3840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'fetch_3840 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'fetch_3466 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.reloc-step
d_reloc'45'step_3842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'step_3842 ~v0 v1 = du_reloc'45'step_3842 v1
du_reloc'45'step_3842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'step_3842 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_reloc'45'step_3444 (coe v0)
      v1 v2 v3 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shift
d_shift_3848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_shift_3848 ~v0 ~v1 = du_shift_3848
du_shift_3848 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_shift_3848
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shift_3128
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shift-loc
d_shift'45'loc_3850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_3850 ~v0 v1 = du_shift'45'loc_3850 v1
du_shift'45'loc_3850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_3850 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shift'45'loc_4040 (coe v0) v1
      v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-branch
d_shifted'45'branch_3852 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_shifted'45'branch_3852 ~v0 ~v1 = du_shifted'45'branch_3852
du_shifted'45'branch_3852 ::
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
du_shifted'45'branch_3852 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'branch_1642 v1 v4
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-call-at
d_shifted'45'call'45'at_3854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'at_3854 ~v0 ~v1
  = du_shifted'45'call'45'at_3854
du_shifted'45'call'45'at_3854 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'at_3854 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'at_1780 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-call-closure
d_shifted'45'call'45'closure_3856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'closure_3856 ~v0 v1
  = du_shifted'45'call'45'closure_3856 v1
du_shifted'45'call'45'closure_3856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'closure_3856 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'closure_1996
      (coe v0) v3 v4 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-call-code
d_shifted'45'call'45'code_3858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'code_3858 ~v0 v1
  = du_shifted'45'call'45'code_3858 v1
du_shifted'45'call'45'code_3858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'code_3858 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'code_1828
      (coe v0) v2 v4 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-call-sv
d_shifted'45'call'45'sv_3860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'sv_3860 ~v0 v1
  = du_shifted'45'call'45'sv_3860 v1
du_shifted'45'call'45'sv_3860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'sv_3860 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'call'45'sv_1910
      (coe v0) v2 v4 v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-eq
d_shifted'45'eq_3862 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shifted'45'eq_3862 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-frame
d_shifted'45'frame_3864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'frame_3864 ~v0 ~v1 = du_shifted'45'frame_3864
du_shifted'45'frame_3864 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'frame_3864 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'frame_1680 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-halt
d_shifted'45'halt_3866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'halt_3866 ~v0 ~v1 = du_shifted'45'halt_3866
du_shifted'45'halt_3866 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'halt_3866 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'halt_1746 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-instr
d_shifted'45'instr_3868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'instr_3868 ~v0 v1 = du_shifted'45'instr_3868 v1
du_shifted'45'instr_3868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'instr_3868 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'instr_2036
      (coe v0) v2 v4 v5 v6 v9
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-jump
d_shifted'45'jump_3870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'jump_3870 ~v0 ~v1 = du_shifted'45'jump_3870
du_shifted'45'jump_3870 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'jump_3870 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'jump_1584 v2 v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-label
d_shifted'45'label_3872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'label_3872 ~v0 ~v1 = du_shifted'45'label_3872
du_shifted'45'label_3872 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'label_3872 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'label_1442 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-ret
d_shifted'45'ret_3874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret_3874 ~v0 ~v1 = du_shifted'45'ret_3874
du_shifted'45'ret_3874 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret_3874 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret_1560 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-ret-aux
d_shifted'45'ret'45'aux_3876 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret'45'aux_3876 ~v0 ~v1
  = du_shifted'45'ret'45'aux_3876
du_shifted'45'ret'45'aux_3876 ::
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret'45'aux_3876 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'ret'45'aux_1508 v2
      v5
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-save-closure
d_shifted'45'save'45'closure_3878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'save'45'closure_3878 ~v0 ~v1
  = du_shifted'45'save'45'closure_3878
du_shifted'45'save'45'closure_3878 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'save'45'closure_3878 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'save'45'closure_1718
      v3
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-shift
d_shifted'45'shift_3880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'shift_3880 ~v0 ~v1 = du_shifted'45'shift_3880
du_shifted'45'shift_3880 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'shift_3880 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'shift_3142
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-straight
d_shifted'45'straight_3882 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'straight_3882 ~v0 ~v1 = du_shifted'45'straight_3882
du_shifted'45'straight_3882 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'straight_3882 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'straight_1406 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.shifted-thunk
d_shifted'45'thunk_3884 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'thunk_3884 ~v0 ~v1 = du_shifted'45'thunk_3884
du_shifted'45'thunk_3884 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'thunk_3884 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_shifted'45'thunk_1470 v4
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.step-dispatch
d_step'45'dispatch_3886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_step'45'dispatch_3886 ~v0 v1 = du_step'45'dispatch_3886 v1
du_step'45'dispatch_3886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_step'45'dispatch_3886 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_step'45'dispatch_3374 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_3888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_3888 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_3890 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_3890 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.sv-is-zero
d_sv'45'is'45'zero_3892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_3892 ~v0 ~v1 = du_sv'45'is'45'zero_3892
du_sv'45'is'45'zero_3892 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_3892
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.tag-zf
d_tag'45'zf_3894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_3894 ~v0 ~v1 = du_tag'45'zf_3894
du_tag'45'zf_3894 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_3894
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.thunk-of?
d_thunk'45'of'63'_3896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_3896 ~v0 ~v1 = du_thunk'45'of'63'_3896
du_thunk'45'of'63'_3896 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_3896
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63'_168
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.thunk-of?-sound
d_thunk'45'of'63''45'sound_3898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_3898 ~v0 ~v1
  = du_thunk'45'of'63''45'sound_3898
du_thunk'45'of'63''45'sound_3898 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_3898 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_thunk'45'of'63''45'sound_476
      v0
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.valid-primitive-wf
d_valid'45'primitive'45'wf_3916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_valid'45'primitive'45'wf_3916 ~v0 ~v1
  = du_valid'45'primitive'45'wf_3916
du_valid'45'primitive'45'wf_3916 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
du_valid'45'primitive'45'wf_3916 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'primitive'45'wf_604
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_3922 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'frontier'45'advance_3922 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4834
      (coe v0) (coe v1) v3 v4 v5 v6 v7 v8 v10 v11 v12
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_3924 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'mem'45'preserved_3924 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                      v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5730
      (coe v0) (coe v1) v3 v4 v5 v7 v8 v11
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_3926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validityWF'45'with'45'bf'45'transfer_3926 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'with'45'bf'45'transfer_5326
      (coe v0) (coe v1) v3 v4 v5 v6 v7 v8 v9 v10
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.vr-mem-pres
d_vr'45'mem'45'pres_3928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vr'45'mem'45'pres_3928 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.μ-layer-iso
d_μ'45'layer'45'iso_3930 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_μ'45'layer'45'iso_3930 ~v0 ~v1 = du_μ'45'layer'45'iso_3930
du_μ'45'layer'45'iso_3930 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
du_μ'45'layer'45'iso_3930 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_μ'45'layer'45'iso_3346
      v7
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.≡ᵇ-true
d_'8801''7495''45'true_3932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_3932 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlockRuns.closures
d_closures_3944 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closures_3944 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_closures_3926
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.BlockRuns.coalgs
d_coalgs_3946 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_3918 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coalgs_3946 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_coalgs_3928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.bf-mono
d_bf'45'mono_3956 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_bf'45'mono_3956 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3836
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.cont-alloc
d_cont'45'alloc_3958 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_3958 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3802
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.events
d_events_3960 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_3960 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.frame-pres
d_frame'45'pres_3962 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_3962 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.live
d_live_3964 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_3964 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.mem-pres
d_mem'45'pres_3966 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_3966 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.no-link
d_no'45'link_3968 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_3968 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.no-ret
d_no'45'ret_3970 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_3970 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.out-mode
d_out'45'mode_3972 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_3972 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3800
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.place
d_place_3974 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618
d_place_3974 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3814
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.returned
d_returned_3976 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_3976 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.run
d_run_3978 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_3978 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3804
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.settle
d_settle_3980 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_3980 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3798
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.CalleeRun.steps
d_steps_3982 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_3740 ->
  Integer
d_steps_3982 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3796
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.falloc
d_falloc_4018 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_4018 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.fclosure
d_fclosure_4020 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_4020 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.flink
d_flink_4022 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_4022 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.floc
d_floc_4024 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_4024 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.fpc
d_fpc_4026 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_4026 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.FlatState.fret
d_fret_4028 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_4028 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.MachineRefinesObsF.traces-agree
d_traces'45'agree_4060 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_4060 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.MachineRefinesObsF.value-realized
d_value'45'realized_4062 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3660 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488
d_value'45'realized_4062 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3690
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.at-end
d_at'45'end_4120 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_4120 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.bf-mono
d_bf'45'mono_4122 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_bf'45'mono_4122 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3588
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.cont-alloc
d_cont'45'alloc_4124 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_4124 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3558
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.frame-pres
d_frame'45'pres_4126 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_4126 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.heap-pres
d_heap'45'pres_4128 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_4128 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.live
d_live_4130 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_4130 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.no-link
d_no'45'link_4132 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_4132 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.no-ret
d_no'45'ret_4134 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_4134 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.out-mode
d_out'45'mode_4136 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_4136 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3556
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.place
d_place_4138 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_618
d_place_4138 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3570
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.run
d_run_4140 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_4140 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3560
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.settle
d_settle_4142 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_4142 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3554
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.stack-pres
d_stack'45'pres_4144 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_4144 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.ValueRealized.steps
d_steps_4146 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3488 ->
  Integer
d_steps_4146 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3552
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_4150 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach._.SMPrimitives.instr-writes-slot
d_instr'45'writes'45'slot_4152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe Integer
d_instr'45'writes'45'slot_4152 ~v0 ~v1
  = du_instr'45'writes'45'slot_4152
du_instr'45'writes'45'slot_4152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Maybe Integer
du_instr'45'writes'45'slot_4152
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_instr'45'writes'45'slot_666
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.flat-store-floc
d_flat'45'store'45'floc_4238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'store'45'floc_4238 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.flat-store-falloc
d_flat'45'store'45'falloc_4252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'store'45'falloc_4252 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.flat-store-fpc
d_flat'45'store'45'fpc_4266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'store'45'fpc_4266 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-preserves-input
d_store'45'ind'45'preserves'45'input_4280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'preserves'45'input_4280 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.load-ind-suc-preserves-input
d_load'45'ind'45'suc'45'preserves'45'input_4312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'ind'45'suc'45'preserves'45'input_4312 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.load-ind-preserves-input
d_load'45'ind'45'preserves'45'input_4366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'ind'45'preserves'45'input_4366 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.load-slot-preserves-input
d_load'45'slot'45'preserves'45'input_4420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'slot'45'preserves'45'input_4420 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-preserves-slot
d_store'45'ind'45'preserves'45'slot_4456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'preserves'45'slot_4456 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.writeLoc-heap-eq
d_writeLoc'45'heap'45'eq_4492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heap'45'eq_4492 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.heap-read-toheap
d_heap'45'read'45'toheap_4520 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'read'45'toheap_4520 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.heap-read-same
d_heap'45'read'45'same_4552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'read'45'same_4552 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-result
d_store'45'ind'45'result_4568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'result_4568 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-suc-result
d_store'45'ind'45'suc'45'result_4596 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'suc'45'result_4596 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.load-slot-result
d_load'45'slot'45'result_4626 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'slot'45'result_4626 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.sucHL-≢
d_sucHL'45''8802'_4654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sucHL'45''8802'_4654 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.heap-untouched
d_heap'45'untouched_4668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'untouched_4668 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-suc-preserves-heap
d_store'45'ind'45'suc'45'preserves'45'heap_4690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'suc'45'preserves'45'heap_4690 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-suc-preserves-slot
d_store'45'ind'45'suc'45'preserves'45'slot_4730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'suc'45'preserves'45'slot_4730 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.mem-untouched
d_mem'45'untouched_4768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'untouched_4768 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-slot-preserves-before
d_store'45'slot'45'preserves'45'before_4806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'preserves'45'before_4806 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.sucHL-ref
d_sucHL'45'ref_4866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucHL'45'ref_4866 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.fresh-heap-≢
d_fresh'45'heap'45''8802'_4878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'heap'45''8802'_4878 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-preserves-before
d_store'45'ind'45'preserves'45'before_4900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'preserves'45'before_4900 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.store-ind-suc-preserves-before
d_store'45'ind'45'suc'45'preserves'45'before_4980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'ind'45'suc'45'preserves'45'before_4980 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.u2
d_u2_5050 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u2_5050 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_u2_5050 v1 v2 v5
du_u2_5050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u2_5050 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
         (coe v1))
      (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.u3
d_u3_5052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u3_5052 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_u3_5052 v1 v2 v5
du_u3_5052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u3_5052 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
         (coe (2 :: Integer)))
      (coe du_u2_5050 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.u4
d_u4_5054 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u4_5054 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_u4_5054 v1 v2 v5
du_u4_5054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u4_5054 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_u3_5052 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.u5
d_u5_5056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u5_5056 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_u5_5056 v1 v2 v5
du_u5_5056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u5_5056 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
      (coe du_u4_5054 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.u6
d_u6_5058 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u6_5058 ~v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_u6_5058 v1 v2 v3 v5
du_u6_5058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u6_5058 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0) (coe v2) (coe du_u5_5056 (coe v0) (coe v1) (coe v3))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.u7
d_u7_5060 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u7_5060 ~v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_u7_5060 v1 v2 v3 v5
du_u7_5060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u7_5060 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
      (coe du_u6_5058 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.u8
d_u8_5062 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u8_5062 ~v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_u8_5062 v1 v2 v3 v4 v5
du_u8_5062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u8_5062 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0) (coe v3)
      (coe du_u7_5060 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.u9
d_u9_5064 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u9_5064 ~v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_u9_5064 v1 v2 v3 v4 v5
du_u9_5064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u9_5064 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
      (coe du_u8_5062 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.u10
d_u10_5066 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u10_5066 ~v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_u10_5066 v1 v2 v3 v4 v5
du_u10_5066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u10_5066 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe du_u9_5064 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.hl
d_hl_5068 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_hl_5068 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_hl_5068 v1 v2 v5
du_hl_5068 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_hl_5068 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
               (coe du_u2_5050 (coe v0) (coe v1) (coe v2)))))
      (coe (0 :: Integer))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.heapref-u2
d_heapref'45'u2_5070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'u2_5070 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.fresh
d_fresh_5072 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_5072 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_fresh_5072 v7
du_fresh_5072 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_5072 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.cf-u3
d_cf'45'u3_5074 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'u3_5074 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.NineStepPres.mem-pres-from
d_mem'45'pres'45'from_5078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'from_5078 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t0
d_t0_5116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t0_5116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_t0_5116 v6 v7 v8 v9
du_t0_5116 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t0_5116 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v1)
      (coe v2) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t1
d_t1_5118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t1_5118 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_t1_5118 v1 v6 v7 v8 v9
du_t1_5118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t1_5118 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
      (coe du_t0_5116 (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.heapref-t1
d_heapref'45't1_5120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45't1_5120 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.cf-t1
d_cf'45't1_5122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45't1_5122 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.cf-u3
d_cf'45'u3_5126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'u3_5126 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.fresh
d_fresh_5128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_5128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_fresh_5128 v8
du_fresh_5128 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_5128 v0 = coe du_fresh_5072 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.heapref-u2
d_heapref'45'u2_5130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'u2_5130 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.hl
d_hl_5132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_hl_5132 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_hl_5132 v1 v2 v6 v7 v8 v9
du_hl_5132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_hl_5132 v0 v1 v2 v3 v4 v5
  = coe
      du_hl_5068 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.mem-pres-from
d_mem'45'pres'45'from_5134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'from_5134 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u10
d_u10_5136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u10_5136 ~v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_u10_5136 v1 v2 v3 v4 v6 v7 v8 v9
du_u10_5136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u10_5136 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_u10_5066 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_t1_5118 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u2
d_u2_5138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u2_5138 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_u2_5138 v1 v2 v6 v7 v8 v9
du_u2_5138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u2_5138 v0 v1 v2 v3 v4 v5
  = coe
      du_u2_5050 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u3
d_u3_5140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u3_5140 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_u3_5140 v1 v2 v6 v7 v8 v9
du_u3_5140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u3_5140 v0 v1 v2 v3 v4 v5
  = coe
      du_u3_5052 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u4
d_u4_5142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u4_5142 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_u4_5142 v1 v2 v6 v7 v8 v9
du_u4_5142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u4_5142 v0 v1 v2 v3 v4 v5
  = coe
      du_u4_5054 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u5
d_u5_5144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u5_5144 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_u5_5144 v1 v2 v6 v7 v8 v9
du_u5_5144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u5_5144 v0 v1 v2 v3 v4 v5
  = coe
      du_u5_5056 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u6
d_u6_5146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u6_5146 ~v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9
  = du_u6_5146 v1 v2 v3 v6 v7 v8 v9
du_u6_5146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u6_5146 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_u6_5058 (coe v0) (coe v1) (coe v2)
      (coe du_t1_5118 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u7
d_u7_5148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u7_5148 ~v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9
  = du_u7_5148 v1 v2 v3 v6 v7 v8 v9
du_u7_5148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u7_5148 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_u7_5060 (coe v0) (coe v1) (coe v2)
      (coe du_t1_5118 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u8
d_u8_5150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u8_5150 ~v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_u8_5150 v1 v2 v3 v4 v6 v7 v8 v9
du_u8_5150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u8_5150 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_u8_5062 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_t1_5118 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.NSP.u9
d_u9_5152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u9_5152 ~v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_u9_5152 v1 v2 v3 v4 v6 v7 v8 v9
du_u9_5152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u9_5152 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_u9_5064 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_t1_5118 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t2
d_t2_5154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t2_5154 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_t2_5154 v1 v2 v6 v7 v8 v9
du_t2_5154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t2_5154 v0 v1 v2 v3 v4 v5
  = coe
      du_u2_5050 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t3
d_t3_5156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t3_5156 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_t3_5156 v1 v2 v6 v7 v8 v9
du_t3_5156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t3_5156 v0 v1 v2 v3 v4 v5
  = coe
      du_u3_5052 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t4
d_t4_5158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t4_5158 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_t4_5158 v1 v2 v6 v7 v8 v9
du_t4_5158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t4_5158 v0 v1 v2 v3 v4 v5
  = coe
      du_u4_5054 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t5
d_t5_5160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t5_5160 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_t5_5160 v1 v2 v6 v7 v8 v9
du_t5_5160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t5_5160 v0 v1 v2 v3 v4 v5
  = coe
      du_u5_5056 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t6
d_t6_5162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t6_5162 ~v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9
  = du_t6_5162 v1 v2 v3 v6 v7 v8 v9
du_t6_5162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t6_5162 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_u6_5058 (coe v0) (coe v1) (coe v2)
      (coe du_t1_5118 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t7
d_t7_5164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t7_5164 ~v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9
  = du_t7_5164 v1 v2 v3 v6 v7 v8 v9
du_t7_5164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t7_5164 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_u7_5060 (coe v0) (coe v1) (coe v2)
      (coe du_t1_5118 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t8
d_t8_5166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t8_5166 ~v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_t8_5166 v1 v2 v3 v4 v6 v7 v8 v9
du_t8_5166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t8_5166 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_u8_5062 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_t1_5118 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t9
d_t9_5168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t9_5168 ~v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_t9_5168 v1 v2 v3 v4 v6 v7 v8 v9
du_t9_5168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t9_5168 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_u9_5064 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_t1_5118 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.t10
d_t10_5170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_t10_5170 ~v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_t10_5170 v1 v2 v3 v4 v6 v7 v8 v9
du_t10_5170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_t10_5170 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_u10_5066 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_t1_5118 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.hl
d_hl_5172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_hl_5172 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_hl_5172 v1 v2 v6 v7 v8 v9
du_hl_5172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_hl_5172 v0 v1 v2 v3 v4 v5
  = coe
      du_hl_5068 (coe v0) (coe v1)
      (coe du_t1_5118 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.heapref-t2
d_heapref'45't2_5174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45't2_5174 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.fresh
d_fresh_5176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_5176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_fresh_5176 v8
du_fresh_5176 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_5176 v0 = coe du_fresh_5072 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.cf-t3
d_cf'45't3_5178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45't3_5178 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.TenStepPres.mem-pres
d_mem'45'pres_5182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_736 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_5182 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.arg-stash
d_arg'45'stash_5216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_arg'45'stash_5216 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_arg'45'stash_5216 v2
du_arg'45'stash_5216 :: Integer -> Integer
du_arg'45'stash_5216 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.env-stash
d_env'45'stash_5218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_env'45'stash_5218 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_env'45'stash_5218 v2
du_env'45'stash_5218 :: Integer -> Integer
du_env'45'stash_5218 v0 = coe addInt (coe (1 :: Integer)) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.pair-stash
d_pair'45'stash_5220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_pair'45'stash_5220 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_pair'45'stash_5220 v2
du_pair'45'stash_5220 :: Integer -> Integer
du_pair'45'stash_5220 v0 = coe addInt (coe (2 :: Integer)) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a0
d_a0_5222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a0_5222 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_a0_5222 v4 v5 v6 v7
du_a0_5222 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a0_5222 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v1)
      (coe v2) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a1
d_a1_5224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a1_5224 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 = du_a1_5224 v1 v4 v5 v6 v7
du_a1_5224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a1_5224 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
      (coe du_a0_5222 (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a2
d_a2_5226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a2_5226 ~v0 v1 v2 ~v3 v4 v5 v6 v7 = du_a2_5226 v1 v2 v4 v5 v6 v7
du_a2_5226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a2_5226 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
         (coe v1))
      (coe du_a1_5224 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a3
d_a3_5228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a3_5228 ~v0 v1 v2 ~v3 v4 v5 v6 v7 = du_a3_5228 v1 v2 v4 v5 v6 v7
du_a3_5228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a3_5228 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
      (coe
         du_a2_5226 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a4
d_a4_5230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a4_5230 ~v0 v1 v2 ~v3 v4 v5 v6 v7 = du_a4_5230 v1 v2 v4 v5 v6 v7
du_a4_5230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a4_5230 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
      (coe
         du_a3_5228 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a5
d_a5_5232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a5_5232 ~v0 v1 v2 ~v3 v4 v5 v6 v7 = du_a5_5232 v1 v2 v4 v5 v6 v7
du_a5_5232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a5_5232 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'save'45'closure_1326
      (coe
         du_a4_5230 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a6
d_a6_5234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a6_5234 ~v0 v1 v2 ~v3 v4 v5 v6 v7 = du_a6_5234 v1 v2 v4 v5 v6 v7
du_a6_5234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a6_5234 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
      (coe
         du_a5_5232 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a7
d_a7_5236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a7_5236 ~v0 v1 v2 ~v3 v4 v5 v6 v7 = du_a7_5236 v1 v2 v4 v5 v6 v7
du_a7_5236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a7_5236 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
         (coe du_env'45'stash_5218 (coe v1)))
      (coe
         du_a6_5234 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a8
d_a8_5238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a8_5238 ~v0 v1 v2 ~v3 v4 v5 v6 v7 = du_a8_5238 v1 v2 v4 v5 v6 v7
du_a8_5238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a8_5238 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
         (coe (2 :: Integer)))
      (coe
         du_a7_5236 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a9
d_a9_5240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a9_5240 ~v0 v1 v2 ~v3 v4 v5 v6 v7 = du_a9_5240 v1 v2 v4 v5 v6 v7
du_a9_5240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a9_5240 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
         (coe du_pair'45'stash_5220 (coe v1)))
      (coe
         du_a8_5238 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a10
d_a10_5242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a10_5242 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_a10_5242 v1 v2 v4 v5 v6 v7
du_a10_5242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a10_5242 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
      (coe
         du_a9_5240 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a11
d_a11_5244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a11_5244 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_a11_5244 v1 v2 v4 v5 v6 v7
du_a11_5244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a11_5244 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
         (coe du_env'45'stash_5218 (coe v1)))
      (coe
         du_a10_5242 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a12
d_a12_5246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a12_5246 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_a12_5246 v1 v2 v4 v5 v6 v7
du_a12_5246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a12_5246 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
      (coe
         du_a11_5244 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a13
d_a13_5248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a13_5248 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_a13_5248 v1 v2 v4 v5 v6 v7
du_a13_5248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a13_5248 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
         (coe v1))
      (coe
         du_a12_5246 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a14
d_a14_5250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a14_5250 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_a14_5250 v1 v2 v4 v5 v6 v7
du_a14_5250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a14_5250 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
      (coe
         du_a13_5248 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a15
d_a15_5252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a15_5252 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_a15_5252 v1 v2 v4 v5 v6 v7
du_a15_5252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a15_5252 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
         (coe du_pair'45'stash_5220 (coe v1)))
      (coe
         du_a14_5250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.a16
d_a16_5254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a16_5254 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_a16_5254 v1 v2 v4 v5 v6 v7
du_a16_5254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a16_5254 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
      (coe
         du_a15_5252 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.ahl
d_ahl_5256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_ahl_5256 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_ahl_5256 v1 v2 v4 v5 v6 v7
du_ahl_5256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_ahl_5256 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
               (coe
                  du_a7_5236 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v5)))))
      (coe (0 :: Integer))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.heapref-a7
d_heapref'45'a7_5258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'a7_5258 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.fresh-a
d_fresh'45'a_5260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh'45'a_5260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_fresh'45'a_5260 v6
du_fresh'45'a_5260 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh'45'a_5260 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a1
d_cf'45'a1_5262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a1_5262 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a6
d_cf'45'a6_5264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a6_5264 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a8
d_cf'45'a8_5266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a8_5266 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a10
d_cf'45'a10_5268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a10_5268 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a12
d_cf'45'a12_5270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a12_5270 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.cf-a14
d_cf'45'a14_5272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a14_5272 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.setup-mem-pres
d_setup'45'mem'45'pres_5276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'mem'45'pres_5276 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.input1-a2
d_input1'45'a2_5292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'a2_5292 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.pair-cell-a2
d_pair'45'cell'45'a2_5306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'cell'45'a2_5306 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf1
d_wf1_5340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf1_5340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9 ~v10 ~v11 ~v12 v13
           ~v14 ~v15 ~v16 ~v17 ~v18
  = du_wf1_5340 v7 v9 v13
du_wf1_5340 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf1_5340 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf3
d_wf3_5342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf3_5342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_wf3_5342 v8 v9
du_wf3_5342 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf3_5342 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v1))
            erased))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.input1-a5
d_input1'45'a5_5344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'a5_5344 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-cell-a5
d_env'45'cell'45'a5_5346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'cell'45'a5_5346 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf6
d_wf6_5348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf6_5348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_wf6_5348 v9 v11
du_wf6_5348 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf6_5348 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh0
d_nh0_5350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh0_5350 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh1
d_nh1_5352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh1_5352 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh2
d_nh2_5354 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh2_5354 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh3
d_nh3_5356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh3_5356 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh4
d_nh4_5358 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh4_5358 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh5
d_nh5_5360 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh5_5360 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh6
d_nh6_5362 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh6_5362 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh7
d_nh7_5364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh7_5364 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh8
d_nh8_5366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh8_5366 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh9
d_nh9_5368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh9_5368 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh10
d_nh10_5370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh10_5370 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-sv'
d_env'45'sv''_5372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_env'45'sv''_5372 ~v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
                   ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_env'45'sv''_5372 v1 v2 v4 v5 v6 v7
du_env'45'sv''_5372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_env'45'sv''_5372 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
            (coe
               du_a6_5234 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-a7
d_env'45'a7_5374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'a7_5374 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-a10
d_env'45'a10_5376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'a10_5376 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.alloc-out
d_alloc'45'out_5378 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'out_5378 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.input1-a10
d_input1'45'a10_5380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'a10_5380 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf11
d_wf11_5384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf11_5384 ~v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_wf11_5384 v1 v2 v4 v5 v6 v7
du_wf11_5384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf11_5384 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_env'45'sv''_5372 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.rdi12'
d_rdi12''_5388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi12''_5388 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.arg-stashed
d_arg'45'stashed_5390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_arg'45'stashed_5390 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11
                      ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_arg'45'stashed_5390 v1 v4 v5 v6 v7
du_arg'45'stashed_5390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_arg'45'stashed_5390 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
            (coe du_a1_5224 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.arg-a2
d_arg'45'a2_5392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'a2_5392 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.arg-a12
d_arg'45'a12_5394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'a12_5394 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf13
d_wf13_5396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf13_5396 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_wf13_5396 v1 v4 v5 v6 v7
du_wf13_5396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf13_5396 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_arg'45'stashed_5390 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
      erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.rdi14'
d_rdi14''_5400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi14''_5400 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.newpair-sv
d_newpair'45'sv_5402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_newpair'45'sv_5402 ~v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11
                     ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_newpair'45'sv_5402 v1 v2 v4 v5 v6 v7
du_newpair'45'sv_5402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_newpair'45'sv_5402 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
            (coe
               du_a8_5238 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.newpair-a9
d_newpair'45'a9_5404 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newpair'45'a9_5404 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.newpair-a14
d_newpair'45'a14_5406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newpair'45'a14_5406 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.wf15
d_wf15_5408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wf15_5408 ~v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_wf15_5408 v1 v2 v4 v5 v6 v7
du_wf15_5408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wf15_5408 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_newpair'45'sv_5402 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh11
d_nh11_5412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh11_5412 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh12
d_nh12_5414 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh12_5414 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh13
d_nh13_5416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh13_5416 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh14
d_nh14_5418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh14_5418 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh15
d_nh15_5420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh15_5420 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nh16
d_nh16_5422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh16_5422 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.input1-a16
d_input1'45'a16_5424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input1'45'a16_5424 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.env-sv'≡
d_env'45'sv'''8801'_5426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'sv'''8801'_5426 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.arg-stashed≡
d_arg'45'stashed'8801'_5428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'stashed'8801'_5428 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.envout-a11
d_envout'45'a11_5430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_envout'45'a11_5430 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.argout-a13
d_argout'45'a13_5432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_argout'45'a13_5432 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.pair-fst-a16
d_pair'45'fst'45'a16_5434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'fst'45'a16_5434 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.pair-snd-a16
d_pair'45'snd'45'a16_5436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'snd'45'a16_5436 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.heapref-a16
d_heapref'45'a16_5438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'a16_5438 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.before-ahl
d_before'45'ahl_5440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_before'45'ahl_5440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_before'45'ahl_5440 v6
du_before'45'ahl_5440 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_before'45'ahl_5440 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680
      (MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.before-ahl-suc
d_before'45'ahl'45'suc_5444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_before'45'ahl'45'suc_5444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_before'45'ahl'45'suc_5444 v6
du_before'45'ahl'45'suc_5444 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_before'45'ahl'45'suc_5444 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680
      (MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.cf-a16
d_cf'45'a16_5448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'a16_5448 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nextslot-a16
d_nextslot'45'a16_5450 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nextslot'45'a16_5450 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.nextslot-a16-≤
d_nextslot'45'a16'45''8804'_5452 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nextslot'45'a16'45''8804'_5452 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
                                 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_nextslot'45'a16'45''8804'_5452 v6
du_nextslot'45'a16'45''8804'_5452 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_nextslot'45'a16'45''8804'_5452 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.heapref-a16-≤
d_heapref'45'a16'45''8804'_5454 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heapref'45'a16'45''8804'_5454 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
                                ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_heapref'45'a16'45''8804'_5454 v6
du_heapref'45'a16'45''8804'_5454 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heapref'45'a16'45''8804'_5454 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.bf-advance
d_bf'45'advance_5462 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_bf'45'advance_5462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_bf'45'advance_5462 v6 v21
du_bf'45'advance_5462 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_bf'45'advance_5462 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_666 v5
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_666
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v5) (coe du_nextslot'45'a16'45''8804'_5452 (coe v0)))
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_676 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_676 v4
             v5 v6 v7
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680 v3
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v3) (coe du_heapref'45'a16'45''8804'_5454 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.carry
d_carry_5484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_carry_5484 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
             ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 v22 v23 ~v24 v25
  = du_carry_5484 v0 v1 v2 v4 v5 v6 v7 v21 v22 v23 v25
du_carry_5484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
du_carry_5484 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4834
      (coe v0) (coe v1) (coe v5)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
         (coe
            du_a16_5254 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)))
      (coe v7) (coe v8) (coe v9)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
         (coe
            du_a16_5254 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)))
      (coe du_nextslot'45'a16'45''8804'_5452 (coe v5))
      (coe du_heapref'45'a16'45''8804'_5454 (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5730
         (coe v0) (coe v1) (coe v5) (coe v7) (coe v8) (coe v4)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
            (coe
               du_a16_5254 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)))
         (coe v10))
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.Obligations.mem-pres
d_mem'45'pres_5500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_5500 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.closure-reg
d_closure'45'reg_5508 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closure'45'reg_5508 = erased
-- Once.CCC.Codegen.IRObsCorrect.Machine.Mach.ApplySetupPres.code-cell
d_code'45'cell_5530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'cell_5530 = erased
