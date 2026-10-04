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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Prelude where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotBudget
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.CCC.Machine.ValidAtWFHalted
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.IRObsCorrect.Prelude.fits-erase
d_fits'45'erase_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518
d_fits'45'erase_16 ~v0 ~v1 ~v2 v3 = du_fits'45'erase_16 v3
du_fits'45'erase_16 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518
du_fits'45'erase_16 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_fits'45'int_202
        -> coe MAlonzo.Code.Once.IRTy.C_fits'45'int_520
      MAlonzo.Code.Once.Type.C_fits'45'float_204
        -> coe MAlonzo.Code.Once.IRTy.C_fits'45'float_522
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.validAtWF-set-halted
d_validAtWF'45'set'45'halted_20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validAtWF'45'set'45'halted_20 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ValidAtWFHalted.du_validAtWF'45'set'45'halted_1328
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v10
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ir-to-trace
d_ir'45'to'45'trace_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace_24 v0 ~v1 = du_ir'45'to'45'trace_24 v0
du_ir'45'to'45'trace_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_ir'45'to'45'trace_24 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_848
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ir-to-trace'
d_ir'45'to'45'trace''_26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_26 v0 ~v1 = du_ir'45'to'45'trace''_26 v0
du_ir'45'to'45'trace''_26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ir'45'to'45'trace''_26 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.budget-of
d_budget'45'of_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_budget'45'of_30 ~v0 ~v1 = du_budget'45'of_30
du_budget'45'of_30 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_budget'45'of_30
  = coe MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_budget'45'of_82
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.frontier-mono
d_frontier'45'mono_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frontier'45'mono_32 v0 ~v1 = du_frontier'45'mono_32 v0
du_frontier'45'mono_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_frontier'45'mono_32 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotBudget.d_frontier'45'mono_164
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.AllI→All
d_AllI'8594'All_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_AllI'8594'All_38 ~v0 ~v1 = du_AllI'8594'All_38
du_AllI'8594'All_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_AllI'8594'All_38 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_AllI'8594'All_202
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.All→AllI
d_All'8594'AllI_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_All'8594'AllI_40 ~v0 ~v1 = du_All'8594'AllI_40
du_All'8594'AllI_40 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_All'8594'AllI_40 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_All'8594'AllI_148
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.BlockStable
d_BlockStable_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockStable_42 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.all-stable?
d_all'45'stable'63'_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> Bool
d_all'45'stable'63'_44 v0 ~v1 = du_all'45'stable'63'_44 v0
du_all'45'stable'63'_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> Bool
du_all'45'stable'63'_44 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_all'45'stable'63'_156
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.all-stable?-++
d_all'45'stable'63''45''43''43'_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45''43''43'_46 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.all-stable?-complete
d_all'45'stable'63''45'complete_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45'complete_48 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.all-stable?-sound
d_all'45'stable'63''45'sound_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'stable'63''45'sound_50 v0 ~v1
  = du_all'45'stable'63''45'sound_50 v0
du_all'45'stable'63''45'sound_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'stable'63''45'sound_50 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_all'45'stable'63''45'sound_178
      (coe v0) v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.bds
d_bds_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bds_52 ~v0 ~v1 = du_bds_52
du_bds_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_bds_52 v0 v1
  = coe MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_bds_706 v1
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.blocks-stable
d_blocks'45'stable_54 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'stable_54 ~v0 ~v1 = du_blocks'45'stable_54
du_blocks'45'stable_54 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'stable_54 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_blocks'45'stable_716
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.cata-body-stable
d_cata'45'body'45'stable_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'body'45'stable_56 ~v0 ~v1 = du_cata'45'body'45'stable_56
du_cata'45'body'45'stable_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'body'45'stable_56 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'body'45'stable_396
      v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.cata-dispatch-slot-stable
d_cata'45'dispatch'45'slot'45'stable_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'dispatch'45'slot'45'stable_58 v0 ~v1
  = du_cata'45'dispatch'45'slot'45'stable_58 v0
du_cata'45'dispatch'45'slot'45'stable_58 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'dispatch'45'slot'45'stable_58 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'dispatch'45'slot'45'stable_512
      (coe v0) v1 v2 v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.cata-trace-branching-stable
d_cata'45'trace'45'branching'45'stable_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'branching'45'stable_60 v0 ~v1
  = du_cata'45'trace'45'branching'45'stable_60 v0
du_cata'45'trace'45'branching'45'stable_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'branching'45'stable_60 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'branching'45'stable_478
      (coe v0) v1 v2 v4 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.cata-trace-const-stable
d_cata'45'trace'45'const'45'stable_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'const'45'stable_62 v0 ~v1
  = du_cata'45'trace'45'const'45'stable_62 v0
du_cata'45'trace'45'const'45'stable_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'const'45'stable_62 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'const'45'stable_416
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.cata-trace-linear-stable
d_cata'45'trace'45'linear'45'stable_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'linear'45'stable_64 v0 ~v1
  = du_cata'45'trace'45'linear'45'stable_64 v0
du_cata'45'trace'45'linear'45'stable_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'linear'45'stable_64 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'linear'45'stable_456
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.cata-trace-nat-stable
d_cata'45'trace'45'nat'45'stable_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'nat'45'stable_66 v0 ~v1
  = du_cata'45'trace'45'nat'45'stable_66 v0
du_cata'45'trace'45'nat'45'stable_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'nat'45'stable_66 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_cata'45'trace'45'nat'45'stable_436
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.ir-blocks-stable
d_ir'45'blocks'45'stable_68 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'blocks'45'stable_68 v0 ~v1
  = du_ir'45'blocks'45'stable_68 v0
du_ir'45'blocks'45'stable_68 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'blocks'45'stable_68 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'blocks'45'stable_810
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.ir-stable
d_ir'45'stable_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_70 v0 ~v1 = du_ir'45'stable_70 v0
du_ir'45'stable_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'stable_70 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'stable_594
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.ir-to-trace-lab-slot-stable
d_ir'45'to'45'trace'45'lab'45'slot'45'stable_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'lab'45'slot'45'stable_72 v0 ~v1
  = du_ir'45'to'45'trace'45'lab'45'slot'45'stable_72 v0
du_ir'45'to'45'trace'45'lab'45'slot'45'stable_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'lab'45'slot'45'stable_72 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'lab'45'slot'45'stable_940
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_74 v0 ~v1
  = du_ir'45'to'45'trace'45'slot'45'stable_74 v0
du_ir'45'to'45'trace'45'slot'45'stable_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'slot'45'stable_74 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_ir'45'to'45'trace'45'slot'45'stable_928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.ir-to-trace-top-slot-stable
d_ir'45'to'45'trace'45'top'45'slot'45'stable_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'top'45'slot'45'stable_76 v0 ~v1
  = du_ir'45'to'45'trace'45'top'45'slot'45'stable_76 v0
du_ir'45'to'45'trace'45'top'45'slot'45'stable_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'top'45'slot'45'stable_76 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_ir'45'to'45'trace'45'top'45'slot'45'stable_954
      (coe v0) v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.rebuild-walk-stable
d_rebuild'45'walk'45'stable_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'walk'45'stable_78 v0 ~v1
  = du_rebuild'45'walk'45'stable_78 v0
du_rebuild'45'walk'45'stable_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'walk'45'stable_78 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_rebuild'45'walk'45'stable_338
      (coe v0) v1 v2 v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.resuspend-stable
d_resuspend'45'stable_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_resuspend'45'stable_80 v0 ~v1 = du_resuspend'45'stable_80 v0
du_resuspend'45'stable_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_resuspend'45'stable_80 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_resuspend'45'stable_740
      (coe v0) v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.sigop-stable
d_sigop'45'stable_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sigop'45'stable_82 v0 ~v1 = du_sigop'45'stable_82 v0
du_sigop'45'stable_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_sigop'45'stable_82 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_sigop'45'stable_568
      (coe v0) v1 v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.stable?
d_stable'63'_84 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> Bool
d_stable'63'_84 v0 ~v1 = du_stable'63'_84 v0
du_stable'63'_84 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> Bool
du_stable'63'_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_stable'63'_154
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.stable?-complete
d_stable'63''45'complete_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable'63''45'complete_86 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.stable?-sound
d_stable'63''45'sound_88 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_stable'63''45'sound_88 v0 ~v1 = du_stable'63''45'sound_88 v0
du_stable'63''45'sound_88 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_stable'63''45'sound_88 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_stable'63''45'sound_174
      (coe v0) v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.trc
d_trc_90 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_trc_90 ~v0 ~v1 = du_trc_90
du_trc_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_trc_90 v0 v1
  = coe MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_trc_142 v1
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.visit-walk-stable
d_visit'45'walk'45'stable_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_visit'45'walk'45'stable_92 v0 ~v1
  = du_visit'45'walk'45'stable_92 v0
du_visit'45'walk'45'stable_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_visit'45'walk'45'stable_92 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.d_visit'45'walk'45'stable_276
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.∧-intro
d_'8743''45'intro_94 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'intro_94 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.CataIRSlotStable.∧-split
d_'8743''45'split_96 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_96 ~v0 ~v1 = du_'8743''45'split_96
du_'8743''45'split_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_96 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable.du_'8743''45'split_170
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.BodyCorrect
d_BodyCorrect_104 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.CellAt
d_CellAt_108 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.CellLocsInRegions
d_CellLocsInRegions_110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 -> ()
d_CellLocsInRegions_110 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF
d_ClosureValidWF_112 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureWellFormed
d_ClosureWellFormed_116 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                        a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.EnvAt
d_EnvAt_120 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRHeapBudget
d_IRHeapBudget_122 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF
d_IRResultAWF_126 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase
d_IRResultBase_130 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget
d_IRStackBudget_134 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InlValidWF
d_InlValidWF_140 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InlineRep
d_InlineRep_144 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InputPlace
d_InputPlace_146 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InrValidWF
d_InrValidWF_148 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.LocInRegions
d_LocInRegions_152 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.LocsInRegions
d_LocsInRegions_154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  ()
d_LocsInRegions_154 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.PairValidWF
d_PairValidWF_156 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.PayloadAt
d_PayloadAt_160 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.Place
d_Place_162 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.RecDispatcherWF
d_RecDispatcherWF_164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> ()
d_RecDispatcherWF_164 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ResultPlace
d_ResultPlace_166 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.SumTag
d_SumTag_168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_168 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_170 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.alloc-correct
d_alloc'45'correct_172 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_172 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.base
d_base_178 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692
d_base_178 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.before-frontier-monotone
d_before'45'frontier'45'monotone_180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_before'45'frontier'45'monotone_180 ~v0 ~v1
  = du_before'45'frontier'45'monotone_180
du_before'45'frontier'45'monotone_180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_before'45'frontier'45'monotone_180 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_before'45'frontier'45'monotone_6962
      v5 v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.body-cap-eq
d_body'45'cap'45'eq_182 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_182 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.body-capacity
d_body'45'capacity_184 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  Integer
d_body'45'capacity_184 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'capacity_1496
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.body-correct
d_body'45'correct_186 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800
d_body'45'correct_186 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'correct_1634
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.bump
d_bump_188 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump_188 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1170
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_190 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_190 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1298
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_192 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_192 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1246
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.code-before
d_code'45'before_198 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_code'45'before_198 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_code'45'before_1626
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.code-ptr
d_code'45'ptr_200 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_200 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.decomposeClosureWF
d_decomposeClosureWF_202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682
d_decomposeClosureWF_202 ~v0 ~v1 = du_decomposeClosureWF_202
du_decomposeClosureWF_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682
du_decomposeClosureWF_202 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1752
      v8
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.decomposeInlWF
d_decomposeInlWF_204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038
d_decomposeInlWF_204 ~v0 ~v1 = du_decomposeInlWF_204
du_decomposeInlWF_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038
du_decomposeInlWF_204 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeInlWF_2128
      v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.decomposeInrWF
d_decomposeInrWF_206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082
d_decomposeInrWF_206 ~v0 ~v1 = du_decomposeInrWF_206
du_decomposeInrWF_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082
du_decomposeInrWF_206 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeInrWF_2170
      v5 v8
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.decomposePairWF
d_decomposePairWF_208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906
d_decomposePairWF_208 ~v0 ~v1 = du_decomposePairWF_208
du_decomposePairWF_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906
du_decomposePairWF_208 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1948
      v8
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.derive-mem-preserved
d_derive'45'mem'45'preserved_210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved_210 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.derive-mem-preserved-at
d_derive'45'mem'45'preserved'45'at_212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved'45'at_212 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.env-before
d_env'45'before_216 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_env'45'before_216 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'before_1624
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.env-ptr
d_env'45'ptr_220 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_220 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.env-valid
d_env'45'valid_222 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_env'45'valid_222 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'valid_1632
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.evalᴰ
d_eval'7472'_224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_224 ~v0 v1 = du_eval'7472'_224 v1
du_eval'7472'_224 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_224 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval'7472'_24
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.execute
d_execute_226 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_226 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_execute_1514
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.final-alloc
d_final'45'alloc_228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_final'45'alloc_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_228 v9 v10
du_final'45'alloc_228 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_final'45'alloc_228 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1200
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.final-state
d_final'45'state_230 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_final'45'state_230 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1166
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.frame-preserved
d_frame'45'preserved_232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_232 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.frontier-slot-stable
d_frontier'45'slot'45'stable_234 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_234 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1256
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.heap-budget
d_heap'45'budget_236 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_heap'45'budget_236 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1294
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.heap-inv
d_heap'45'inv_238 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710
d_heap'45'inv_238 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.heap-monotone
d_heap'45'monotone_240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_240 v9
du_heap'45'monotone_240 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_240 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1304
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.heap-preserved-of
d_heap'45'preserved'45'of_242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'preserved'45'of_242 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.inline-sv
d_inline'45'sv_250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_590 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_250 ~v0 ~v1 = du_inline'45'sv_250
du_inline'45'sv_250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_590 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_250 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_600
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.input-read
d_input'45'read_252 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'read_252 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.input-sv
d_input'45'sv_254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_input'45'sv_254 ~v0 ~v1 = du_input'45'sv_254
du_input'45'sv_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_input'45'sv_254 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_input'45'sv_1844
      v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.inputPlace-transport
d_inputPlace'45'transport_256 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InputPlace_1812
d_inputPlace'45'transport_256 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inputPlace'45'transport_5592
      (coe v0) (coe v1) v2 v3 v5 v6 v7 v8 v9 v10 v12 v13
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ir-returns
d_ir'45'returns_258 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_ir'45'returns_258 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ir'45'returns_1180
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.irresult-mem-preserved
d_irresult'45'mem'45'preserved_260 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irresult'45'mem'45'preserved_260 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.loc-mem-eq-from-regions
d_loc'45'mem'45'eq'45'from'45'regions_270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
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
d_loc'45'mem'45'eq'45'from'45'regions_270 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.mEnv
d_mEnv_272 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_272 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_mEnv_1630
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_274 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_274 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1300
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.max-heap-ref-written
d_max'45'heap'45'ref'45'written_276 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_max'45'heap'45'ref'45'written_276 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1296
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_278 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_278 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1302
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.max-slot-geq-final
d_max'45'slot'45'geq'45'final_280 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_280 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1248
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_282 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_282 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1250
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.max-slot-written
d_max'45'slot'45'written_284 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_max'45'slot'45'written_284 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1242
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.mem-preserved-before
d_mem'45'preserved'45'before_286 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_286 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.mem-preserved-compose
d_mem'45'preserved'45'compose_288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
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
d_mem'45'preserved'45'compose_288 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.mem-preserved-from-tnhw
d_mem'45'preserved'45'from'45'tnhw_290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'from'45'tnhw_290 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.mk-IRResultAWF-via-bump
d_mk'45'IRResultAWF'45'via'45'bump_292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
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
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726
d_mk'45'IRResultAWF'45'via'45'bump_292 ~v0 ~v1
  = du_mk'45'IRResultAWF'45'via'45'bump_292
du_mk'45'IRResultAWF'45'via'45'bump_292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
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
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726
du_mk'45'IRResultAWF'45'via'45'bump_292 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
                                        v24 v25
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_mk'45'IRResultAWF'45'via'45'bump_784
      v8 v10 v11 v16 v17 v18 v21 v23 v24 v25
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.not-halted
d_not'45'halted_294 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_294 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.obs-budget
d_obs'45'budget_296 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_obs'45'budget_296 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1178
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.payload-read
d_payload'45'read_302 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'read_302 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.payload-sv
d_payload'45'sv_304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_payload'45'sv_304 ~v0 ~v1 = du_payload'45'sv_304
du_payload'45'sv_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_payload'45'sv_304 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_payload'45'sv_2000
      v3 v6
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.place-rax
d_place'45'rax_306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_place'45'rax_306 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.place-sv
d_place'45'sv_308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_place'45'sv_308 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_place'45'sv_660
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.prim-sv
d_prim'45'sv_310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_310 ~v0 ~v1 = du_prim'45'sv_310
du_prim'45'sv_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_310 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_582
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.reclaim-alloc
d_reclaim'45'alloc_312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_reclaim'45'alloc_312 ~v0 ~v1 = du_reclaim'45'alloc_312
du_reclaim'45'alloc_312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_reclaim'45'alloc_312 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_reclaim'45'alloc_6642
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.reclaim-preserves-frontier
d_reclaim'45'preserves'45'frontier_314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_reclaim'45'preserves'45'frontier_314 ~v0 ~v1
  = du_reclaim'45'preserves'45'frontier_314
du_reclaim'45'preserves'45'frontier_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_reclaim'45'preserves'45'frontier_314 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_reclaim'45'preserves'45'frontier_6656
      v3 v4 v5
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.result-place
d_result'45'place_320 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_result'45'place_320 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1182
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.scratch-bounded
d_scratch'45'bounded_322 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_322 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1268
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.scratch-budget
d_scratch'45'budget_324 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_scratch'45'budget_324 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1266
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.slot-monotone
d_slot'45'monotone_326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_326 v9
du_slot'45'monotone_326 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_326 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1270
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_328 v9 v10
du_slot'45'stays'45'in'45'budget_328 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_328 v0 v1
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
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.stack-budget
d_stack'45'budget_330 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_stack'45'budget_330 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1244
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.stack-inv
d_stack'45'inv_332 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702
d_stack'45'inv_332 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.sucLoc-before
d_sucLoc'45'before_334 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_334 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1628
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace
d_trace_336 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_trace_336 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1168
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace-correct
d_trace'45'correct_338 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_338 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_340 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_340 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_342 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_342 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1198
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace-preserves-halted
d_trace'45'preserves'45'halted_344 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_344 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_346 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_346 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1260
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_348 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_348 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1264
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace-twf
d_trace'45'twf_350 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_trace'45'twf_350 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1190
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace-writes-above
d_trace'45'writes'45'above_352 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'writes'45'above_352 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1258
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.trace-writes-below
d_trace'45'writes'45'below_354 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'writes'45'below_354 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1262
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.transport-SumTag
d_transport'45'SumTag_356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_transport'45'SumTag_356 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.valid-primitive-wf
d_valid'45'primitive'45'wf_378 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_valid'45'primitive'45'wf_378 ~v0 ~v1
  = du_valid'45'primitive'45'wf_378
du_valid'45'primitive'45'wf_378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_valid'45'primitive'45'wf_378 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'primitive'45'wf_632
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.valid-to-validWF-unit
d_valid'45'to'45'validWF'45'unit_380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_valid'45'to'45'validWF'45'unit_380 ~v0 ~v1
  = du_valid'45'to'45'validWF'45'unit_380
du_valid'45'to'45'validWF'45'unit_380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_valid'45'to'45'validWF'45'unit_380 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_valid'45'to'45'validWF'45'unit_2206
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-alloc-advance
d_validityWF'45'alloc'45'advance_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'alloc'45'advance_388 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'alloc'45'advance_4100
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v10
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'frontier'45'advance_390 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'frontier'45'advance_4440
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v11 v12 v13
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-mem-only
d_validityWF'45'mem'45'only_392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'mem'45'only_392 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'only_2222
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'mem'45'preserved_394 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v12
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-mem-preserved-excluding
d_validityWF'45'mem'45'preserved'45'excluding_396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'mem'45'preserved'45'excluding_396 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_validityWF'45'mem'45'preserved'45'excluding_5646
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-mem-preserved-in-regions
d_validityWF'45'mem'45'preserved'45'in'45'regions_398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
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
d_validityWF'45'mem'45'preserved'45'in'45'regions_398 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_validityWF'45'mem'45'preserved'45'in'45'regions_6636
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-mem-preserved-in-regions-strong
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
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
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_400 v0
                                                                v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                v12 v13 v14 v15 v16 v17 v18 v19 v20
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042
      (coe v0) (coe v1) v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v19 v20
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-reclaim
d_validityWF'45'reclaim_402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'reclaim_402 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'reclaim_6740
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v10 v12
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-trace-preserves
d_validityWF'45'trace'45'preserves_404 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'trace'45'preserves_404 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'trace'45'preserves_6880
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664) ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'with'45'bf'45'transfer_406 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'with'45'bf'45'transfer_4856
      (coe v0) (coe v1) v2 v4 v5 v6 v7 v8 v9 v10 v11
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-write-at-frontier
d_validityWF'45'write'45'at'45'frontier_408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'write'45'at'45'frontier_408 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'at'45'frontier_2610
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-write-at-suc-frontier
d_validityWF'45'write'45'at'45'suc'45'frontier_410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'write'45'at'45'suc'45'frontier_410 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'at'45'suc'45'frontier_2982
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-write-sv-at-frontier
d_validityWF'45'write'45'sv'45'at'45'frontier_412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'write'45'sv'45'at'45'frontier_412 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'sv'45'at'45'frontier_3354
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.validityWF-write-sv-at-suc-frontier
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_414 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_414 v0 v1 v2
                                                         v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726
      (coe v0) (coe v1) v2 v4 v5 v6 v8 v9 v11
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ιᶠ
d_ι'7584'_416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_ι'7584'_416 ~v0 ~v1 = du_ι'7584'_416
du_ι'7584'_416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
du_ι'7584'_416
  = coe MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_ι'7584'_26
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.μ-validity-in-regions-stub
d_μ'45'validity'45'in'45'regions'45'stub_418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_μ'45'validity'45'in'45'regions'45'stub_418 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_μ'45'validity'45'in'45'regions'45'stub_5984
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ν-validity-in-regions-stub
d_ν'45'validity'45'in'45'regions'45'stub_420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_ν'45'validity'45'in'45'regions'45'stub_420 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ν'45'validity'45'in'45'regions'45'stub_6010
      v0 v1
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.BodyCorrect.body-cap-eq
d_body'45'cap'45'eq_424 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_424 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.BodyCorrect.body-capacity
d_body'45'capacity_426 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  Integer
d_body'45'capacity_426 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'capacity_1496
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.BodyCorrect.execute
d_execute_428 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_428 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_execute_1514
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF.EnvType
d_EnvType_438 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_438 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_EnvType_1716
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF.body
d_body_440 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_body_440 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body_1718
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF.body-label
d_body'45'label_442 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_442 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'label_1722
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF.code-ptr
d_code'45'ptr_444 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_444 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF.env
d_env_446 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  AgdaAny
d_env_446 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env_1720 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF.env-at
d_env'45'at_448 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1648
d_env'45'at_448 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'at_1726
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_450 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_450 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF.loc-mode
d_loc'45'mode_452 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  AgdaAny
d_loc'45'mode_452 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_loc'45'mode_1724
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_454 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_454 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1730
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureWellFormed.body-correct
d_body'45'correct_458 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_BodyCorrect_800
d_body'45'correct_458 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'correct_1634
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureWellFormed.code-before
d_code'45'before_460 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_code'45'before_460 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_code'45'before_1626
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureWellFormed.code-ptr
d_code'45'ptr_462 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_462 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureWellFormed.env-before
d_env'45'before_464 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_env'45'before_464 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'before_1624
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureWellFormed.env-ptr
d_env'45'ptr_466 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_466 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureWellFormed.env-valid
d_env'45'valid_468 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_env'45'valid_468 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'valid_1632
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureWellFormed.mEnv
d_mEnv_470 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_470 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_mEnv_1630
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.ClosureWellFormed.sucLoc-before
d_sucLoc'45'before_472 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_472 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1628
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRHeapBudget.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_482 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_482 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1298
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRHeapBudget.heap-budget
d_heap'45'budget_484 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  Integer
d_heap'45'budget_484 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1294
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRHeapBudget.heap-monotone
d_heap'45'monotone_486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_486 ~v0 ~v1 = du_heap'45'monotone_486
du_heap'45'monotone_486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_486 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1304
      v1
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_488 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_488 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1300
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-written
d_max'45'heap'45'ref'45'written_490 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  Integer
d_max'45'heap'45'ref'45'written_490 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1296
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRHeapBudget.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_492 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_492 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1302
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.alloc-correct
d_alloc'45'correct_496 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_496 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.base
d_base_498 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692
d_base_498 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.bump
d_bump_500 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump_500 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1170
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_502 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_502 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'heap'45'budget_1298
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_504 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_504 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1246
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.final-alloc
d_final'45'alloc_506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_final'45'alloc_506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_506 v9 v10
du_final'45'alloc_506 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_final'45'alloc_506 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1200
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.final-state
d_final'45'state_508 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_final'45'state_508 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1166
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.frame-preserved
d_frame'45'preserved_510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_510 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.frontier-slot-stable
d_frontier'45'slot'45'stable_512 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_512 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1256
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.heap-budget
d_heap'45'budget_514 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_heap'45'budget_514 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'budget_1294
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.heap-inv
d_heap'45'inv_516 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRHeapBudget_710
d_heap'45'inv_516 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.heap-monotone
d_heap'45'monotone_518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_518 v9
du_heap'45'monotone_518 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_518 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_heap'45'monotone_1304
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.ir-returns
d_ir'45'returns_520 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_ir'45'returns_520 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ir'45'returns_1180
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_522 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_522 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'geq'45'final_1300
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.max-heap-ref-written
d_max'45'heap'45'ref'45'written_524 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_max'45'heap'45'ref'45'written_524 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'ref'45'written_1296
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_526 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_526 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'heap'45'usage'45'bound_1302
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_heap'45'inv_1332
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.max-slot-geq-final
d_max'45'slot'45'geq'45'final_528 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_528 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1248
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_530 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_530 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1250
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.max-slot-written
d_max'45'slot'45'written_532 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_max'45'slot'45'written_532 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1242
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.mem-preserved-before
d_mem'45'preserved'45'before_534 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_534 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.not-halted
d_not'45'halted_536 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_536 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.obs-budget
d_obs'45'budget_538 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_obs'45'budget_538 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1178
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.result-place
d_result'45'place_540 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_result'45'place_540 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1182
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.scratch-bounded
d_scratch'45'bounded_542 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_542 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1268
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.scratch-budget
d_scratch'45'budget_544 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_scratch'45'budget_544 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1266
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.slot-monotone
d_slot'45'monotone_546 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_546 v9
du_slot'45'monotone_546 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_546 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1270
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_548 v9 v10
du_slot'45'stays'45'in'45'budget_548 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_548 v0 v1
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
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.stack-budget
d_stack'45'budget_550 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  Integer
d_stack'45'budget_550 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1244
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.stack-inv
d_stack'45'inv_552 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702
d_stack'45'inv_552 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace
d_trace_554 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_trace_554 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1168
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace-correct
d_trace'45'correct_556 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_556 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_558 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_558 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_560 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_560 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1198
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace-preserves-halted
d_trace'45'preserves'45'halted_562 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_562 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_564 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_564 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1260
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_566 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_566 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1264
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace-twf
d_trace'45'twf_568 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_trace'45'twf_568 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1190
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_base_1328
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace-writes-above
d_trace'45'writes'45'above_570 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'writes'45'above_570 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1258
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultAWF.trace-writes-below
d_trace'45'writes'45'below_572 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultAWF_726 ->
  AgdaAny
d_trace'45'writes'45'below_572 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1262
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'inv_1330
         (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.alloc-correct
d_alloc'45'correct_576 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_576 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.bump
d_bump_578 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump_578 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump_1170
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.final-alloc
d_final'45'alloc_580 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_final'45'alloc_580 ~v0 ~v1 = du_final'45'alloc_580
du_final'45'alloc_580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_final'45'alloc_580 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_final'45'alloc_1200
      v7 v8
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.final-state
d_final'45'state_582 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_final'45'state_582 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_final'45'state_1166
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.frame-preserved
d_frame'45'preserved_584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_584 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.ir-returns
d_ir'45'returns_586 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  AgdaAny
d_ir'45'returns_586 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_ir'45'returns_1180
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.mem-preserved-before
d_mem'45'preserved'45'before_588 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_588 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.not-halted
d_not'45'halted_590 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_590 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.obs-budget
d_obs'45'budget_592 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  Integer
d_obs'45'budget_592 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_obs'45'budget_1178
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.result-place
d_result'45'place_594 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_result'45'place_594 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_result'45'place_1182
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.trace
d_trace_596 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_trace_596 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace_1168
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.trace-correct
d_trace'45'correct_598 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_598 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_600 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_600 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_602 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  AgdaAny
d_trace'45'no'45'frame'45'ops_602 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'no'45'frame'45'ops_1198
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.trace-preserves-halted
d_trace'45'preserves'45'halted_604 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_604 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRResultBase.trace-twf
d_trace'45'twf_606 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_trace'45'twf_606 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'twf_1190
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_610 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_610 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_bump'45'fits'45'stack'45'budget_1246
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.frontier-slot-stable
d_frontier'45'slot'45'stable_612 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_612 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_frontier'45'slot'45'stable_1256
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.max-slot-geq-final
d_max'45'slot'45'geq'45'final_614 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_614 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'geq'45'final_1248
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_616 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_616 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'usage'45'bound_1250
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.max-slot-written
d_max'45'slot'45'written_618 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  Integer
d_max'45'slot'45'written_618 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_max'45'slot'45'written_1242
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.scratch-bounded
d_scratch'45'bounded_620 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_620 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'bounded_1268
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.scratch-budget
d_scratch'45'budget_622 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  Integer
d_scratch'45'budget_622 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_scratch'45'budget_1266
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.slot-monotone
d_slot'45'monotone_624 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_624 ~v0 ~v1 = du_slot'45'monotone_624
du_slot'45'monotone_624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_624 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'monotone_1270
      v1
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_626 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_626 ~v0 ~v1
  = du_slot'45'stays'45'in'45'budget_626
du_slot'45'stays'45'in'45'budget_626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_626 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_slot'45'stays'45'in'45'budget_1272
      v1 v2 v5
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.stack-budget
d_stack'45'budget_628 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  Integer
d_stack'45'budget_628 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_stack'45'budget_1244
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_630 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  AgdaAny
d_trace'45'slot'45'reads'45'above_630 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'above_1260
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_632 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  AgdaAny
d_trace'45'slot'45'reads'45'below_632 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'slot'45'reads'45'below_1264
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.trace-writes-above
d_trace'45'writes'45'above_634 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  AgdaAny
d_trace'45'writes'45'above_634 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'above_1258
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.IRStackBudget.trace-writes-below
d_trace'45'writes'45'below_636 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_IRStackBudget_702 ->
  AgdaAny
d_trace'45'writes'45'below_636 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_trace'45'writes'45'below_1262
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InlValidWF.a
d_a_640 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038 ->
  AgdaAny
d_a_640 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_a_2060 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InlValidWF.payload
d_payload_642 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968
d_payload_642 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_payload_2064
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InlValidWF.sucLoc-before
d_sucLoc'45'before_644 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_644 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_2062
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InlValidWF.v-is-inl
d_v'45'is'45'inl_646 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlValidWF_2038 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_646 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InrValidWF.b
d_b_664 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082 ->
  AgdaAny
d_b_664 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_b_2104 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InrValidWF.payload
d_payload_666 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PayloadAt_1968
d_payload_666 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_payload_2108
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InrValidWF.sucLoc-before
d_sucLoc'45'before_668 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_668 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_2106
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.InrValidWF.v-is-inr
d_v'45'is'45'inr_670 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InrValidWF_2082 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_670 = erased
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.PairValidWF.fst-cell
d_fst'45'cell_684 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612
d_fst'45'cell_684 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1928
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.PairValidWF.snd-cell
d_snd'45'cell_686 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612
d_snd'45'cell_686 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1930
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Prelude._.ClosureWellFormedDef.PairValidWF.sucLoc-before
d_sucLoc'45'before_688 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_688 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_sucLoc'45'before_1926
      (coe v0)
